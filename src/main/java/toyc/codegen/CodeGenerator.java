package toyc.codegen;

import toyc.parser.ast.*;
import toyc.semantic.SemanticAnalyzer;
import toyc.semantic.Symbol;

import java.util.*;

/**
 * Generates RISC-V32 (RV32IM) assembly from annotated AST.
 */
public class CodeGenerator {

    private final SemanticAnalyzer analyzer;
    private final boolean optimize;
    // Register cache DISABLED: stable-register approach causes correctness
    // bugs (wrong output on p01-p05, timeouts on p06-p12). Requires proper
    // liveness analysis and SSA-based register allocation to work safely.
    // The simpler optimizations below are safe and still provide good speedups.
    private static final boolean enableRegCache = false;
    private final StringBuilder sb;
    private int labelCounter;
    private final Deque<LoopLabels> loopStack;

    // Registers for expression evaluation
    private static final String[] TEMP_REGS = {"t0", "t1", "t2", "t3", "t4", "t5", "t6"};
    private static final int NUM_TEMPS = 7;
    private final boolean[] tempUsed = new boolean[NUM_TEMPS];
    // Overflow pool: a0-a7, used only when t-regs exhausted.
    private static final String[] A_REGS = {"a0","a1","a2","a3","a4","a5","a6","a7"};
    private static final int NUM_A_REGS = 8;
    private final boolean[] aUsed = new boolean[NUM_A_REGS];
    private static final String[] SAVED_VALUE_REGS = {
            "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"
    };

    // Current function context
    private FuncDef currentFunc;
    private boolean currentFuncIsLeaf;
    private final Deque<Map<String, Integer>> localOffsetStack = new ArrayDeque<>(); // scoped variable → offset from fp
    private int nextLocalOffset; // grows downward (negative)

    // Frame info
    private int frameSize;
    private int savedValueRegCount;

    // Function-local symbols assigned to callee-saved registers.
    private final Map<Symbol, String> symbolRegs = new IdentityHashMap<>();

    // Register cache for local variables (optimization)
    // Simple "last store" tracking: maps variable name → register from most
    // recent store. If the register hasn't been reused, the next read can
    // skip the lw and use the register directly. Much simpler and safer
    // than full register caching — only tracks one use, no stable registers.
    private final Map<String, String> lastStoreReg = new HashMap<>();
    // Registers that still hold their last-stored value (not yet reused).
    private final Set<String> regValid = new HashSet<>();

    // Full register cache (disabled — too complex, causes correctness bugs)
    private final Map<String, String> varRegCache = new HashMap<>();
    private final Map<String, String> regToVar = new HashMap<>();
    private final Set<String> varDirty = new HashSet<>();

    // Loop labels
    private record LoopLabels(String start, String end) {}

    public CodeGenerator(SemanticAnalyzer analyzer, boolean optimize) {
        this.analyzer = analyzer;
        this.optimize = optimize;
        this.sb = new StringBuilder();
        this.labelCounter = 0;
        this.loopStack = new ArrayDeque<>();
    }

    // ========== Entry point ==========

    public String generate(CompUnit compUnit) {
        // Emit .data section for global variables/constants
        StringBuilder dataSection = new StringBuilder();
        boolean hasData = false;

        for (ASTNode item : compUnit.items()) {
            if (item instanceof VarDecl vd) {
                Integer val = analyzer.evalConst(vd.initExpr());
                if (val == null) {
                    val = 0; // default if cannot evaluate
                }
                dataSection.append("  .globl ").append(vd.name()).append("\n");
                dataSection.append(vd.name()).append(":\n");
                dataSection.append("  .word ").append(val).append("\n");
                hasData = true;
            } else if (item instanceof ConstDecl cd) {
                Integer val = analyzer.evalConst(cd.initExpr());
                if (val != null) {
                    dataSection.append("  .globl ").append(cd.name()).append("\n");
                    dataSection.append(cd.name()).append(":\n");
                    dataSection.append("  .word ").append(val).append("\n");
                    hasData = true;
                }
            }
        }

        if (hasData) {
            emit(".data");
            sb.append(dataSection);
            emit("");
        }

        emit(".text");
        emit(".globl main");
        emit("");

        for (ASTNode item : compUnit.items()) {
            if (item instanceof FuncDef fd) {
                genFuncDef(fd);
            }
        }

        return sb.toString();
    }

    // ========== Function definition ==========

    private void genFuncDef(FuncDef fd) {
        currentFunc = fd;
        localOffsetStack.clear();
        localOffsetStack.push(new HashMap<>()); // function scope
        freeSpillSlots.clear();
        varRegCache.clear();
        regToVar.clear();
        varDirty.clear();
        lastStoreReg.clear();
        regValid.clear();
        symbolRegs.clear();
        Arrays.fill(tempUsed, false);
        Arrays.fill(aUsed, false);
        nextLocalOffset = -8; // skip past saved ra (-4) and saved fp (-8)

        // Count locals declared in the body
        countLocals(fd.body());

        // Determine whether this is a leaf function (no calls in body)
        // and whether parameters can be kept in a0-a7 registers.
        boolean isLeaf = !stmtContainsCall(fd.body());
        currentFuncIsLeaf = isLeaf;

        Symbol funcSym = analyzer.getFuncSymbols().get(fd);
        assignSavedRegisters(fd);
        boolean leafParamsKeptInRegs = false;
        if (isLeaf && funcSym != null && funcSym.getFuncParamNames() != null) {
            leafParamsKeptInRegs = true;
            if (funcSym.getFuncParamNames().size() > 8) {
                leafParamsKeptInRegs = false;
            }
            for (String pn : funcSym.getFuncParamNames()) {
                if (stmtAssignsTo(fd.body(), pn)) {
                    leafParamsKeptInRegs = false;
                    break;
                }
            }
        }

        // Pre-allocate slots for parameters only if they'll be stored to stack.
        if (!leafParamsKeptInRegs && funcSym != null
                && funcSym.getFuncParamNames() != null) {
            for (String paramName : funcSym.getFuncParamNames()) {
                getLocalOffset(paramName);
            }
        }

        // Save the final offset for frame calculation, then reset for code gen.
        // countLocals and getLocalOffset above advance nextLocalOffset but pop
        // block scopes, so genStmt must restart from -8 to produce matching offsets.
        int finalLocalOffset = nextLocalOffset;

        // Reserve spill slots for expression evaluation.
        // calcMaxSpillDepth covers binary-expr and per-call spills.
        // Add headroom for nested-call scenarios where outer genCall
        // pre-spills coexist with inner genCall arg-eval spills.
        int maxSpillDepth = calcMaxSpillDepth(fd.body());
        if (!isLeaf) {
            maxSpillDepth += 12; // safety margin for nested-call overlaps
        }
        int spillAreaSize = maxSpillDepth * 4;

        savedValueRegCount = symbolRegs.size();
        boolean hasLocalsOrParams = finalLocalOffset < -8;
        boolean needsFrame = hasLocalsOrParams || maxSpillDepth > 0;
        if (savedValueRegCount > 0) {
            needsFrame = true;
        }

        // Calculate frame size.
        int savedRegsSize = (needsFrame || !isLeaf) ? 8 + savedValueRegCount * 4 : 0;

        int localSize = -finalLocalOffset - 8;
        if (localSize < 0) localSize = 0;
        frameSize = savedRegsSize + localSize + spillAreaSize;
        frameSize = (frameSize + 15) & ~15; // 16-byte aligned

        // Emit function label
        emit("");
        emitLabel(fd.name());

        // Prologue
        if (frameSize > 0) {
            emit("addi", "sp", "sp", String.valueOf(-frameSize));
            if (!isLeaf) {
                emit("sw", "ra", (frameSize - 4) + "(sp)");
            }
            emit("sw", "s0", (frameSize - 8) + "(sp)");
            for (int i = 0; i < savedValueRegCount; i++) {
                emit("sw", SAVED_VALUE_REGS[i], (frameSize - 12 - i * 4) + "(sp)");
            }
            emit("addi", "s0", "sp", String.valueOf(frameSize));
        }

        // Reset local offset state for code generation.
        // countLocals already consumed offset space; genStmt must replay
        // the same allocations starting from -8 so offsets match the frame.
        nextLocalOffset = -8;
        localOffsetStack.clear();
        localOffsetStack.push(new HashMap<>()); // function scope

        // Re-run parameter pre-allocation so genStmt/genId can find them.
        if (!leafParamsKeptInRegs && funcSym != null
                && funcSym.getFuncParamNames() != null) {
            for (String paramName : funcSym.getFuncParamNames()) {
                getLocalOffset(paramName);
            }
        }

        // Set up spill slot area for code generation (below all locals/params).
        nextSpillOffset = finalLocalOffset - 4;

        // Store parameters into local slots.
        List<Symbol> paramSymbols = analyzer.getFuncParamSymbols().get(fd);
        if (paramSymbols != null && frameSize > 0) {
            for (int i = 0; i < paramSymbols.size(); i++) {
                String reg = symbolRegs.get(paramSymbols.get(i));
                if (reg == null) continue;
                if (i < 8) {
                    emit("mv", reg, "a" + i);
                } else {
                    int callerOff = frameSize + (i - 8) * 4;
                    emit("lw", reg, callerOff + "(sp)");
                }
            }
        }
        if (!leafParamsKeptInRegs && funcSym != null
                && funcSym.getFuncParamNames() != null && frameSize > 0) {
            int argReg = 0;
            for (String paramName : funcSym.getFuncParamNames()) {
                Symbol paramSym = paramSymbols != null && argReg < paramSymbols.size()
                        ? paramSymbols.get(argReg) : null;
                if (symbolRegs.containsKey(paramSym)) {
                    argReg++;
                    continue;
                }
                if (argReg < 8) {
                    String reg = "a" + argReg;
                    int offset = getLocalOffset(paramName);
                    emit("sw", reg, offset + "(s0)");
                } else {
                    String reg = allocReg();
                    int callerOff = frameSize + (argReg - 8) * 4;
                    int offset = getLocalOffset(paramName);
                    emit("lw", reg, callerOff + "(sp)");
                    emit("sw", reg, offset + "(s0)");
                    freeReg(reg);
                }
                argReg++;
            }
        }

        // Generate body
        genStmt(fd.body());

        // Epilogue
        emitLabel(funcEpilogueLabel());
        if (frameSize > 0) {
            if (!isLeaf) {
                emit("lw", "ra", (frameSize - 4) + "(sp)");
            }
            for (int i = 0; i < savedValueRegCount; i++) {
                emit("lw", SAVED_VALUE_REGS[i], (frameSize - 12 - i * 4) + "(sp)");
            }
            emit("lw", "s0", (frameSize - 8) + "(sp)");
            emit("addi", "sp", "sp", String.valueOf(frameSize));
        }
        emit("ret");

        currentFunc = null;
    }

    private String funcEpilogueLabel() {
        return ".L.epilogue." + currentFunc.name();
    }

    // ========== Count locals ==========

    private void countLocals(Stmt stmt) {
        switch (stmt) {
            case Block b -> {
                localOffsetStack.push(new HashMap<>());
                for (Stmt s : b.stmts()) countLocals(s);
                localOffsetStack.pop();
            }
            case VarDecl vd -> allocateLocal(vd.name());
            case ConstDecl cd -> allocateLocal(cd.name());
            case IfStmt is -> {
                countLocals(is.thenStmt());
                if (is.elseStmt() != null) countLocals(is.elseStmt());
            }
            case WhileStmt ws -> countLocals(ws.body());
            default -> {}
        }
    }

    private void assignSavedRegisters(FuncDef fd) {
        if (!optimize) return;

        IdentityHashMap<Symbol, Integer> weights = new IdentityHashMap<>();
        collectSymbolWeights(fd.body(), weights, 0);

        List<Symbol> paramSymbols = analyzer.getFuncParamSymbols().get(fd);
        if (paramSymbols != null) {
            for (Symbol sym : paramSymbols) {
                weights.putIfAbsent(sym, 0);
            }
        }

        List<Map.Entry<Symbol, Integer>> candidates = new ArrayList<>();
        for (Map.Entry<Symbol, Integer> entry : weights.entrySet()) {
            Symbol sym = entry.getKey();
            if (sym == null || sym.isGlobal() || sym.isConst() || sym.isFunc()) continue;
            if (entry.getValue() < 8) continue;
            candidates.add(entry);
        }
        candidates.sort((a, b) -> Integer.compare(b.getValue(), a.getValue()));

        int n = Math.min(SAVED_VALUE_REGS.length, candidates.size());
        for (int i = 0; i < n; i++) {
            symbolRegs.put(candidates.get(i).getKey(), SAVED_VALUE_REGS[i]);
        }
    }

    private void collectSymbolWeights(Stmt stmt, IdentityHashMap<Symbol, Integer> weights, int loopDepth) {
        switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) {
                    collectSymbolWeights(s, weights, loopDepth);
                }
            }
            case ExprStmt es -> collectExprWeights(es.expr(), weights, loopDepth);
            case AssignStmt as_ -> {
                addWeight(weights, analyzer.getAssignSymbols().get(as_), weightFor(loopDepth) + 2);
                collectExprWeights(as_.value(), weights, loopDepth);
            }
            case VarDecl vd -> {
                addWeight(weights, analyzer.getVarDeclSymbols().get(vd), 1);
                collectExprWeights(vd.initExpr(), weights, loopDepth);
            }
            case ConstDecl cd -> collectExprWeights(cd.initExpr(), weights, loopDepth);
            case IfStmt is -> {
                collectExprWeights(is.condition(), weights, loopDepth);
                collectSymbolWeights(is.thenStmt(), weights, loopDepth);
                if (is.elseStmt() != null) collectSymbolWeights(is.elseStmt(), weights, loopDepth);
            }
            case WhileStmt ws -> {
                collectExprWeights(ws.condition(), weights, loopDepth + 1);
                collectSymbolWeights(ws.body(), weights, loopDepth + 1);
            }
            case ReturnStmt rs -> {
                if (rs.value() != null) collectExprWeights(rs.value(), weights, loopDepth);
            }
            default -> {}
        }
    }

    private void collectExprWeights(Expr expr, IdentityHashMap<Symbol, Integer> weights, int loopDepth) {
        switch (expr) {
            case IdExpr id -> addWeight(weights, analyzer.getIdSymbols().get(id), weightFor(loopDepth));
            case BinaryExpr be -> {
                collectExprWeights(be.left(), weights, loopDepth);
                collectExprWeights(be.right(), weights, loopDepth);
            }
            case UnaryExpr ue -> collectExprWeights(ue.operand(), weights, loopDepth);
            case CallExpr ce -> {
                for (Expr arg : ce.args()) collectExprWeights(arg, weights, loopDepth);
            }
            default -> {}
        }
    }

    private int weightFor(int loopDepth) {
        return loopDepth == 0 ? 1 : 8 * loopDepth;
    }

    private void addWeight(IdentityHashMap<Symbol, Integer> weights, Symbol sym, int delta) {
        if (sym == null || sym.isGlobal() || sym.isConst() || sym.isFunc()) return;
        weights.merge(sym, delta, Integer::sum);
    }

    /**
     * Count the maximum number of simultaneously-live spill slots needed
     * for binary expression evaluation. This equals the maximum depth
     * of binary expression nesting within any statement.
     */
    private int calcMaxSpillDepth(Stmt stmt) {
        return switch (stmt) {
            case Block b -> {
                int maxD = 0;
                for (Stmt s : b.stmts()) {
                    maxD = Math.max(maxD, calcMaxSpillDepth(s));
                }
                yield maxD;
            }
            case IfStmt is -> {
                int d = calcMaxExprDepth(is.condition());
                d = Math.max(d, calcMaxSpillDepth(is.thenStmt()));
                if (is.elseStmt() != null) d = Math.max(d, calcMaxSpillDepth(is.elseStmt()));
                yield d;
            }
            case WhileStmt ws -> {
                int d = calcMaxExprDepth(ws.condition());
                d = Math.max(d, calcMaxSpillDepth(ws.body()));
                yield d;
            }
            case ExprStmt es -> calcMaxExprDepth(es.expr());
            case AssignStmt as_ -> calcMaxExprDepth(as_.value());
            case VarDecl vd -> calcMaxExprDepth(vd.initExpr());
            case ConstDecl cd -> calcMaxExprDepth(cd.initExpr());
            case ReturnStmt rs -> rs.value() != null ? calcMaxExprDepth(rs.value()) : 0;
            default -> 0;
        };
    }

    /**
     * Calculate the max binary-expr nesting depth in an expression.
     * Each binary expression needs one spill slot during evaluation;
     * nested binary expressions need one spill slot per level.
     * Short-circuit operators (&&, ||) don't use spill slots.
     */
    private int calcMaxExprDepth(Expr expr) {
        return switch (expr) {
            case BinaryExpr be -> {
                if ("&&".equals(be.op()) || "||".equals(be.op())) {
                    // Short-circuit ops don't use spill slots
                    yield Math.max(calcMaxExprDepth(be.left()),
                                   calcMaxExprDepth(be.right()));
                }
                // Regular binary: a spill is only needed if the right operand
                // (or the left operand evaluation) contains a function call.
                if (!exprContainsCall(be.right())) {
                    // No call in right operand → genBinary skips the spill.
                    yield Math.max(calcMaxExprDepth(be.left()),
                                   calcMaxExprDepth(be.right()));
                }
                // Right contains a call → a spill IS needed at this level.
                int leftDepth = calcMaxExprDepth(be.left());
                int rightDepth = calcMaxExprDepth(be.right());
                yield Math.max(leftDepth, 1 + rightDepth);
            }
            case UnaryExpr ue -> calcMaxExprDepth(ue.operand());
            case CallExpr ce -> {
                int maxD = 0;
                for (Expr arg : ce.args()) {
                    maxD = Math.max(maxD, calcMaxExprDepth(arg));
                }
                // genCall may spill previously-evaluated register args
                // before evaluating call-containing args. Conservative
                // upper bound: all register args spilled at once.
                int callSpills = Math.min(ce.args().size(), 8);
                yield maxD + callSpills;
            }
            default -> 0;
        };
    }

    private int allocateLocal(String name) {
        Map<String, Integer> currentScope = localOffsetStack.peek();
        if (currentScope.containsKey(name)) {
            return currentScope.get(name);
        }
        nextLocalOffset -= 4;
        currentScope.put(name, nextLocalOffset);
        return nextLocalOffset;
    }

    private int getLocalOffset(String name) {
        // Search from innermost scope outward
        for (Map<String, Integer> scope : localOffsetStack) {
            Integer off = scope.get(name);
            if (off != null) return off;
        }
        // For parameters not yet allocated — put in function scope (bottom)
        nextLocalOffset -= 4;
        localOffsetStack.peekLast().put(name, nextLocalOffset);
        return nextLocalOffset;
    }

    /**
     * Look up a variable's offset without auto-creating.
     * Returns null if the name is not found in any local scope.
     */
    private Integer lookupLocalOffset(String name) {
        for (Map<String, Integer> scope : localOffsetStack) {
            Integer off = scope.get(name);
            if (off != null) return off;
        }
        return null;
    }

    // ========== Register cache for local variables (optimization) ==========

    /** Cache a variable's value in a register. */
    private void cacheVar(String name, String reg) {
        if (!optimize || !enableRegCache) return;
        // If this variable was previously cached in a different register,
        // free the old register.
        String oldReg = varRegCache.get(name);
        if (oldReg != null && !oldReg.equals(reg)) {
            regToVar.remove(oldReg);
            freeRegRaw(oldReg);
        }
        // If this register was holding another variable, remove that mapping.
        String oldVar = regToVar.get(reg);
        if (oldVar != null && !oldVar.equals(name)) {
            varRegCache.remove(oldVar);
            varDirty.remove(oldVar);
        }
        varRegCache.put(name, reg);
        regToVar.put(reg, name);
        varDirty.add(name);
    }

    /** Get the register holding a variable's value, or null. */
    private String getCachedReg(String name) {
        if (!optimize) return null;
        return varRegCache.get(name);
    }

    /** Flush (store to stack) a cached variable if dirty. */
    private void flushVar(String name) {
        if (!optimize) return;
        if (!varDirty.contains(name)) return;
        String reg = varRegCache.get(name);
        if (reg == null) return;
        Integer off = lookupLocalOffset(name);
        if (off != null) {
            emit("sw", reg, off + "(s0)");
        }
        varDirty.remove(name);
    }

    /** Flush all dirty cached variables to stack. */
    private void flushAllDirty() {
        if (!optimize) return;
        for (String name : new ArrayList<>(varDirty)) {
            flushVar(name);
        }
    }

    /** Invalidate register cache (before function calls). */
    private void invalidateRegCache() {
        if (!optimize) return;
        // Flush dirty vars first to preserve their values in memory
        flushAllDirty();
        // Free all cached registers (keys are register names like "t0")
        for (String reg : new ArrayList<>(regToVar.keySet())) {
            freeRegRaw(reg);
        }
        varRegCache.clear();
        regToVar.clear();
        varDirty.clear();
    }

    /** Invalidate a specific variable from cache (when it goes out of scope). */
    private void invalidateVar(String name) {
        if (!optimize) return;
        flushVar(name);
        String reg = varRegCache.remove(name);
        if (reg != null) {
            regToVar.remove(reg);
            freeRegRaw(reg);
        }
        varDirty.remove(name);
    }

    // ========== Statement generation ==========

    private void genStmt(Stmt stmt) {
        switch (stmt) {
            case Block b -> {
                localOffsetStack.push(new HashMap<>());
                // Track vars declared in this block for scope cleanup
                Set<String> blockVars = new HashSet<>();
                for (Stmt s : b.stmts()) {
                    if (s instanceof VarDecl vd) blockVars.add(vd.name());
                    else if (s instanceof ConstDecl cd) blockVars.add(cd.name());
                    genStmt(s);
                }
                // Flush and invalidate block-scoped variables on exit.
                // Also clean up any last-store register entries so the
                // registers don't stay marked as "used" after the block.
                for (String name : blockVars) {
                    invalidateVar(name);
                    if (optimize) {
                        String lsReg = lastStoreReg.remove(name);
                        if (lsReg != null) {
                            regValid.remove(lsReg);
                            freeRegRaw(lsReg);
                        }
                    }
                }
                localOffsetStack.pop();
            }
            case NullStmt ignored -> {}
            case ExprStmt es -> {
                // Dead code elimination: if expression has no side effects, skip
                if (optimize && isPureExpr(es.expr())) {
                    return;
                }
                String r = genExpr(es.expr());
                freeReg(r);
            }
            case AssignStmt as_ -> {
                Symbol targetSym = analyzer.getAssignSymbols().get(as_);
                String savedReg = symbolRegs.get(targetSym);
                if (savedReg != null && tryEmitAssignToSavedReg(as_, targetSym, savedReg)) {
                    return;
                }
                String r = genExpr(as_.value());
                savedReg = symbolRegs.get(targetSym);
                if (savedReg != null) {
                    if (!savedReg.equals(r)) {
                        emit("mv", savedReg, r);
                    }
                    if (optimize) {
                        String lsReg = lastStoreReg.remove(as_.name());
                        if (lsReg != null) regValid.remove(lsReg);
                    }
                    freeReg(r);
                    return;
                }
                // Check local scope first (handles shadowing of globals)
                Integer localOff = lookupLocalOffset(as_.name());
                if (localOff != null) {
                    if (optimize) {
                        // Keep variable in its existing cached register if any
                        String cachedReg = getCachedReg(as_.name());
                        if (cachedReg != null && !cachedReg.equals(r)) {
                            emit("mv", cachedReg, r);
                            freeReg(r);
                            r = cachedReg;
                        }
                        cacheVar(as_.name(), r);
                        varDirty.remove(as_.name()); // stored below
                    }
                    emit("sw", r, localOff + "(s0)");
                } else {
                    Symbol sym = analyzer.getGlobalScope().lookup(as_.name());
                    if (sym != null && sym.isGlobal() && !sym.isConst()) {
                        // Store to global variable
                        String addrReg = allocReg();
                        emit("la", addrReg, sym.getName());
                        emit("sw", r, "0(" + addrReg + ")");
                        freeReg(addrReg);
                    } else {
                        // Parameter or other local not yet allocated
                        int offset = getLocalOffset(as_.name());
                        if (optimize) {
                            String cachedReg = getCachedReg(as_.name());
                            if (cachedReg != null && !cachedReg.equals(r)) {
                                emit("mv", cachedReg, r);
                                freeReg(r);
                                r = cachedReg;
                            }
                            cacheVar(as_.name(), r);
                            varDirty.remove(as_.name());
                        }
                        emit("sw", r, offset + "(s0)");
                    }
                }
                if (optimize) {
                    // Last-store optimization: keep register alive for next read
                    lastStoreReg.put(as_.name(), r);
                    regValid.add(r);
                } else {
                    freeReg(r);
                }
            }
            case VarDecl vd -> {
                // Dead code elimination: only skip if variable is never used
                // AND the initializer is pure (no side effects).
                if (optimize && !isVarUsed(vd.name(), currentFunc.body())
                        && isPureExpr(vd.initExpr())) {
                    // Still allocate offset for frame size compatibility
                    allocateLocal(vd.name());
                    return;
                }
                String savedReg = symbolRegs.get(analyzer.getVarDeclSymbols().get(vd));
                if (savedReg != null && vd.initExpr() instanceof LiteralExpr le) {
                    allocateLocal(vd.name());
                    emit("li", savedReg, String.valueOf(le.value()));
                    return;
                }
                String r = genExpr(vd.initExpr());
                int offset = allocateLocal(vd.name());
                savedReg = symbolRegs.get(analyzer.getVarDeclSymbols().get(vd));
                if (savedReg != null) {
                    emit("mv", savedReg, r);
                    freeReg(r);
                    return;
                }
                if (optimize && enableRegCache) {
                    cacheVar(vd.name(), r);
                    varDirty.remove(vd.name()); // stored below
                }
                emit("sw", r, offset + "(s0)");
                if (optimize) {
                    lastStoreReg.put(vd.name(), r);
                    regValid.add(r);
                } else {
                    freeReg(r);
                }
            }
            case ConstDecl cd -> {
                if (optimize) {
                    allocateLocal(cd.name());
                    return;
                }
                if (optimize && !isVarUsed(cd.name(), currentFunc.body())) {
                    if (hasSideEffects(cd.initExpr())) {
                        String r = genExpr(cd.initExpr());
                        freeReg(r);
                    }
                    allocateLocal(cd.name());
                    return;
                }
                String r = genExpr(cd.initExpr());
                int offset = allocateLocal(cd.name());
                emit("sw", r, offset + "(s0)");
                if (optimize) {
                    lastStoreReg.put(cd.name(), r);
                    regValid.add(r);
                } else {
                    freeReg(r);
                }
            }
            case IfStmt is -> genIf(is);
            case WhileStmt ws -> genWhile(ws);
            case BreakStmt bs -> {
                LoopLabels lbls = loopStack.peek();
                if (lbls != null) {
                    emit("j", lbls.end());
                }
            }
            case ContinueStmt cs -> {
                LoopLabels lbls = loopStack.peek();
                if (lbls != null) {
                    emit("j", lbls.start());
                }
            }
            case ReturnStmt rs -> genReturn(rs);
            default -> {}
        }
    }

    private void genIf(IfStmt is) {
        String elseLabel = newLabel("else");
        String endLabel = newLabel("if_end");

        // Condition: non-zero is true
        String condReg = genExpr(is.condition());
        emit("beqz", condReg, is.elseStmt() != null ? elseLabel : endLabel);
        freeReg(condReg);

        // Then branch
        genStmt(is.thenStmt());

        if (is.elseStmt() != null) {
            emit("j", endLabel);
            emitLabel(elseLabel);
            genStmt(is.elseStmt());
        }
        emitLabel(endLabel);
    }

    private void genWhile(WhileStmt ws) {
        String startLabel = newLabel("while_start");
        String bodyLabel = newLabel("while_body");
        String endLabel = newLabel("while_end");

        loopStack.push(new LoopLabels(startLabel, endLabel));

        emitLabel(startLabel);
        String condReg = genExpr(ws.condition());
        emit("beqz", condReg, endLabel);
        freeReg(condReg);

        emitLabel(bodyLabel);
        genStmt(ws.body());
        emit("j", startLabel);

        emitLabel(endLabel);
        loopStack.pop();
    }

    private void genReturn(ReturnStmt rs) {
        flushAllDirty();
        if (rs.value() != null) {
            if (optimize && rs.value() instanceof LiteralExpr le) {
                emit("li", "a0", String.valueOf(le.value()));
                emit("j", funcEpilogueLabel());
                return;
            }
            if (optimize && rs.value() instanceof IdExpr id) {
                Symbol sym = analyzer.getIdSymbols().get(id);
                if (sym != null && sym.isConst() && sym.getConstValue() != null) {
                    emit("li", "a0", String.valueOf(sym.getConstValue()));
                    emit("j", funcEpilogueLabel());
                    return;
                }
                String savedReg = symbolRegs.get(sym);
                if (savedReg != null) {
                    emit("mv", "a0", savedReg);
                    emit("j", funcEpilogueLabel());
                    return;
                }
            }
            String r = genExpr(rs.value());
            emit("mv", "a0", r); // return value in a0
            freeReg(r);
        }
        // Jump to epilogue
        emit("j", funcEpilogueLabel());
    }

    private boolean tryEmitAssignToSavedReg(AssignStmt stmt, Symbol targetSym, String targetReg) {
        Expr value = stmt.value();

        if (value instanceof LiteralExpr le) {
            emit("li", targetReg, String.valueOf(le.value()));
            return true;
        }
        if (value instanceof IdExpr id) {
            Symbol valueSym = analyzer.getIdSymbols().get(id);
            if (valueSym == targetSym) return true;
            if (valueSym != null && valueSym.isConst() && valueSym.getConstValue() != null) {
                emit("li", targetReg, String.valueOf(valueSym.getConstValue()));
                return true;
            }
            String sourceReg = symbolRegs.get(valueSym);
            if (sourceReg != null) {
                emit("mv", targetReg, sourceReg);
                return true;
            }
            return false;
        }
        if (value instanceof UnaryExpr ue) {
            if (ue.operand() instanceof IdExpr id && analyzer.getIdSymbols().get(id) == targetSym) {
                switch (ue.op()) {
                    case "+" -> { return true; }
                    case "-" -> { emit("sub", targetReg, "zero", targetReg); return true; }
                    case "!" -> { emit("seqz", targetReg, targetReg); return true; }
                    default -> { return false; }
                }
            }
            return false;
        }
        if (value instanceof BinaryExpr be) {
            if ("&&".equals(be.op()) || "||".equals(be.op())) return false;

            if (be.left() instanceof IdExpr leftId
                    && analyzer.getIdSymbols().get(leftId) == targetSym) {
                if (be.right() instanceof LiteralExpr rle
                        && tryEmitRightLiteralOp(be.op(), targetReg, rle.value())) {
                    return true;
                }
                if (be.right() instanceof IdExpr rightId) {
                    Symbol rightSym = analyzer.getIdSymbols().get(rightId);
                    if (rightSym != null && rightSym.isConst() && rightSym.getConstValue() != null
                            && tryEmitRightLiteralOp(be.op(), targetReg, rightSym.getConstValue())) {
                        return true;
                    }
                    String rightSavedReg = symbolRegs.get(rightSym);
                    if (rightSavedReg != null) {
                        emitBinaryOp(be.op(), targetReg, targetReg, rightSavedReg);
                        return true;
                    }
                }
                String rightReg = genExpr(be.right());
                emitBinaryOp(be.op(), targetReg, targetReg, rightReg);
                freeReg(rightReg);
                return true;
            }

            if (isCommutative(be.op())
                    && be.right() instanceof IdExpr rightId
                    && analyzer.getIdSymbols().get(rightId) == targetSym) {
                if (be.left() instanceof IdExpr leftId) {
                    String leftSavedReg = symbolRegs.get(analyzer.getIdSymbols().get(leftId));
                    if (leftSavedReg != null) {
                        emitBinaryOp(be.op(), targetReg, leftSavedReg, targetReg);
                        return true;
                    }
                }
                String leftReg = genExpr(be.left());
                emitBinaryOp(be.op(), targetReg, leftReg, targetReg);
                freeReg(leftReg);
                return true;
            }
        }
        return false;
    }

    private boolean isCommutative(String op) {
        return "+".equals(op) || "*".equals(op) || "==".equals(op) || "!=".equals(op);
    }

    private void emitBinaryOp(String op, String rd, String leftReg, String rightReg) {
        switch (op) {
            case "+" -> emit("add", rd, leftReg, rightReg);
            case "-" -> emit("sub", rd, leftReg, rightReg);
            case "*" -> emit("mul", rd, leftReg, rightReg);
            case "/" -> emit("div", rd, leftReg, rightReg);
            case "%" -> emit("rem", rd, leftReg, rightReg);
            case "==" -> {
                emit("sub", rd, leftReg, rightReg);
                emit("seqz", rd, rd);
            }
            case "!=" -> {
                emit("sub", rd, leftReg, rightReg);
                emit("snez", rd, rd);
            }
            case "<"  -> emit("slt", rd, leftReg, rightReg);
            case ">=" -> {
                emit("slt", rd, leftReg, rightReg);
                emit("xori", rd, rd, "1");
            }
            case ">"  -> emit("slt", rd, rightReg, leftReg);
            case "<=" -> {
                emit("slt", rd, rightReg, leftReg);
                emit("xori", rd, rd, "1");
            }
            default -> emit("add", rd, leftReg, rightReg);
        }
    }

    // ========== Expression generation ==========

    /**
     * Generate code for an expression, returning the register holding the result.
     */
    private String genExpr(Expr expr) {
        return switch (expr) {
            case LiteralExpr le -> genLiteral(le);
            case IdExpr id -> genId(id);
            case BinaryExpr be -> genBinary(be);
            case UnaryExpr ue -> genUnary(ue);
            case CallExpr ce -> genCall(ce);
        };
    }

    private String genLiteral(LiteralExpr le) {
        String r = allocReg();
        emit("li", r, String.valueOf(le.value()));
        return r;
    }

    private String genId(IdExpr id) {
        Symbol sym = analyzer.getIdSymbols().get(id);
        if (sym == null) {
            String r = allocReg();
            emit("li", r, "0"); // error recovery
            return r;
        }
        if (sym.isConst() && sym.getConstValue() != null) {
            // Inline constant value
            String r = allocReg();
            emit("li", r, String.valueOf(sym.getConstValue()));
            return r;
        }

        String savedReg = symbolRegs.get(sym);
        if (savedReg != null) {
            String r = allocReg();
            emit("mv", r, savedReg);
            return r;
        }

        // Persistent last-store cache: if variable's register is still
        // valid, copy it to a new temp register without consuming.
        // The cache survives multiple reads until the register is
        // stolen by allocReg or the variable is reassigned.
        if (optimize) {
            String lsReg = lastStoreReg.get(id.name());
            if (lsReg != null && regValid.contains(lsReg)) {
                String r = allocReg();
                emit("mv", r, lsReg);
                return r;
            }
        }

        String r = allocReg();
        if (sym.isGlobal()) {
            // Load from global address: la r, sym; lw r, 0(r)
            emit("la", r, sym.getName());
            emit("lw", r, "0(" + r + ")");
        } else if (currentFuncIsLeaf && sym.getKind() == Symbol.Kind.PARAM
                && lookupLocalOffset(id.name()) == null) {
            // Leaf function: parameter kept in its original a-register
            // (not assigned to, not stored to stack).
            // Find which parameter index this is.
            Symbol funcSym = analyzer.getFuncSymbols().get(currentFunc);
            int paramIdx = -1;
            if (funcSym != null && funcSym.getFuncParamNames() != null) {
                paramIdx = funcSym.getFuncParamNames().indexOf(id.name());
            }
            if (paramIdx >= 0 && paramIdx < 8) {
                emit("mv", r, "a" + paramIdx);
            } else if (paramIdx >= 8 && frameSize > 0) {
                int callerOff = frameSize + (paramIdx - 8) * 4;
                emit("lw", r, callerOff + "(sp)");
            } else {
                emit("li", r, "0");
            }
        } else {
            int offset = getLocalOffset(id.name());
            emit("lw", r, offset + "(s0)");
        }
        return r;
    }

    private String genBinary(BinaryExpr be) {
        // Short-circuit evaluation for && and ||
        if ("&&".equals(be.op())) {
            return genLogicalAnd(be);
        }
        if ("||".equals(be.op())) {
            return genLogicalOr(be);
        }

        // Constant folding: if both operands are compile-time constants
        if (optimize) {
            Integer constVal = tryConstantFold(be);
            if (constVal != null) {
                String r = allocReg();
                emit("li", r, String.valueOf(constVal));
                return r;
            }
        }

        String leftReg = genExpr(be.left());
        if (optimize && be.right() instanceof LiteralExpr rle) {
            int imm = rle.value();
            if (tryEmitRightLiteralOp(be.op(), leftReg, imm)) {
                return leftReg;
            }
        }

        // Only spill left if the right operand contains a function call
        // (which may clobber caller-saved temp registers t0-t6).
        String rightReg;
        String resultReg;

        if (exprContainsCall(be.right())) {
            // Right operand contains a call — spill left to frame.
            int spillOffset = allocateSpillSlot();
            spillReg(leftReg, spillOffset);
            freeReg(leftReg);

            rightReg = genExpr(be.right());
            resultReg = loadSpill(spillOffset);
            freeSpillSlot(spillOffset);
        } else {
            // Right operand has no calls — reuse leftReg as result to avoid mv.
            rightReg = genExpr(be.right());
            resultReg = leftReg;
            // Don't free leftReg — it's now resultReg
        }

        // Algebraic identities and strength reduction
        if (optimize) {
            // Right-side literal identities
            if (be.right() instanceof LiteralExpr rle) {
                int imm = rle.value();
                boolean handled = false;
                switch (be.op()) {
                    case "+" -> { if (imm == 0) handled = true; }
                    case "-" -> { if (imm == 0) handled = true; }
                    case "*" -> {
                        if (imm == 0) { emit("mv", resultReg, "zero"); handled = true; }
                        else if (imm == 1) handled = true;
                        else if ((imm & (imm - 1)) == 0 && imm > 0) {
                            emit("slli", resultReg, resultReg,
                                 String.valueOf(Integer.numberOfTrailingZeros(imm)));
                            handled = true;
                        }
                    }
                    case "/" -> { if (imm == 1) handled = true; }
                    case "%" -> { if (imm == 1) { emit("mv", resultReg, "zero"); handled = true; } }
                }
                if (handled) { freeReg(rightReg); return resultReg; }
                if (tryEmitImmOp(be.op(), resultReg, resultReg, imm)) {
                    freeReg(rightReg); return resultReg;
                }
            }
            // Left-side literal commutative identities
            if (be.left() instanceof LiteralExpr lle) {
                int imm = lle.value();
                boolean handled = false;
                switch (be.op()) {
                    case "+" -> { if (imm == 0) { freeReg(resultReg); return rightReg; } }
                    case "*" -> {
                        if (imm == 0) { emit("mv", resultReg, "zero"); handled = true; }
                        else if (imm == 1) { freeReg(resultReg); return rightReg; }
                    }
                    case "-" -> {
                        if (imm == 0) { emit("sub", resultReg, "zero", rightReg); handled = true; }
                    }
                }
                if (handled) { freeReg(rightReg); return resultReg; }
            }
        }

        // resultReg holds left value; apply operator with rightReg
        switch (be.op()) {
            case "+" -> emit("add", resultReg, resultReg, rightReg);
            case "-" -> emit("sub", resultReg, resultReg, rightReg);
            case "*" -> emit("mul", resultReg, resultReg, rightReg);
            case "/" -> emit("div", resultReg, resultReg, rightReg);
            case "%" -> emit("rem", resultReg, resultReg, rightReg);
            case "==" -> {
                emit("sub", resultReg, resultReg, rightReg);
                emit("seqz", resultReg, resultReg);
            }
            case "!=" -> {
                emit("sub", resultReg, resultReg, rightReg);
                emit("snez", resultReg, resultReg);
            }
            case "<"  -> emit("slt", resultReg, resultReg, rightReg);
            case ">=" -> {
                emit("slt", resultReg, resultReg, rightReg);
                emit("xori", resultReg, resultReg, "1");
            }
            case ">"  -> emit("slt", resultReg, rightReg, resultReg);
            case "<=" -> {
                emit("slt", resultReg, rightReg, resultReg);
                emit("xori", resultReg, resultReg, "1");
            }
            default -> emit("add", resultReg, resultReg, rightReg);
        }
        freeReg(rightReg);
        return resultReg;
    }

    /** Try to evaluate a binary expression at compile time. */
    private Integer tryConstantFold(BinaryExpr be) {
        Integer l = getConstVal(be.left());
        Integer r = getConstVal(be.right());
        if (l == null || r == null) return null;
        return switch (be.op()) {
            case "+" -> l + r;
            case "-" -> l - r;
            case "*" -> l * r;
            case "/" -> { if (r == 0) yield null; yield l / r; }
            case "%" -> { if (r == 0) yield null; yield l % r; }
            case "==" -> l.equals(r) ? 1 : 0;
            case "!=" -> l.equals(r) ? 0 : 1;
            case "<"  -> l < r ? 1 : 0;
            case ">"  -> l > r ? 1 : 0;
            case "<=" -> l <= r ? 1 : 0;
            case ">=" -> l >= r ? 1 : 0;
            default -> null;
        };
    }

    /** Get constant value from an expression, or null. */
    private Integer getConstVal(Expr expr) {
        return switch (expr) {
            case LiteralExpr le -> le.value();
            case IdExpr id -> {
                Symbol sym = analyzer.getIdSymbols().get(id);
                if (sym != null && sym.isConst() && sym.getConstValue() != null)
                    yield sym.getConstValue();
                yield null;
            }
            case UnaryExpr ue -> {
                Integer op = getConstVal(ue.operand());
                if (op == null) yield null;
                yield switch (ue.op()) {
                    case "-" -> -op;
                    case "!" -> (op == 0) ? 1 : 0;
                    default -> op;
                };
            }
            case BinaryExpr be -> tryConstantFold(be);
            default -> null;
        };
    }

    /** Try to emit an immediate-form instruction. Returns true if successful. */
    private boolean tryEmitImmOp(String op, String rd, String rs, int imm) {
        switch (op) {
            case "+" -> {
                if (!isImm12(imm)) return false;
                emit("addi", rd, rs, String.valueOf(imm)); return true;
            }
            case "-" -> {
                if (!isImm12(-imm)) return false;
                emit("addi", rd, rs, String.valueOf(-imm)); return true;
            }
            case "<" -> {
                if (!isImm12(imm)) return false;
                emit("slti", rd, rs, String.valueOf(imm)); return true;
            }
            case ">=" -> {
                if (!isImm12(imm)) return false;
                emit("slti", rd, rs, String.valueOf(imm));
                emit("xori", rd, rd, "1"); return true;
            }
            case ">" -> {
                if (imm < 2047 && isImm12(imm + 1)) {
                    emit("slti", rd, rs, String.valueOf(imm + 1));
                    emit("xori", rd, rd, "1"); return true;
                } else return false;
            }
            case "<=" -> {
                if (imm < 2047 && isImm12(imm + 1)) {
                    emit("slti", rd, rs, String.valueOf(imm + 1));
                    return true;
                } else return false;
            }
            case "==" -> {
                if (!isImm12(-imm)) return false;
                if (imm == 0) emit("seqz", rd, rs);
                else { emit("addi", rd, rs, String.valueOf(-imm)); emit("seqz", rd, rd); }
                return true;
            }
            case "!=" -> {
                if (!isImm12(-imm)) return false;
                if (imm == 0) emit("snez", rd, rs);
                else { emit("addi", rd, rs, String.valueOf(-imm)); emit("snez", rd, rd); }
                return true;
            }
            default -> { return false; }
        }
    }

    private boolean tryEmitRightLiteralOp(String op, String rd, int imm) {
        switch (op) {
            case "+" -> {
                if (imm == 0) return true;
                return tryEmitImmOp(op, rd, rd, imm);
            }
            case "-" -> {
                if (imm == 0) return true;
                return tryEmitImmOp(op, rd, rd, imm);
            }
            case "*" -> {
                if (imm == 0) { emit("mv", rd, "zero"); return true; }
                if (imm == 1) return true;
                if (imm > 0 && (imm & (imm - 1)) == 0) {
                    emit("slli", rd, rd, String.valueOf(Integer.numberOfTrailingZeros(imm)));
                    return true;
                }
                return false;
            }
            case "/" -> {
                if (imm == 1) return true;
                if (imm == -1) { emit("sub", rd, "zero", rd); return true; }
                return false;
            }
            case "%" -> {
                if (imm == 1 || imm == -1) { emit("mv", rd, "zero"); return true; }
                return false;
            }
            case "<", ">", "<=", ">=", "==", "!=" -> {
                return tryEmitImmOp(op, rd, rd, imm);
            }
            default -> {
                return false;
            }
        }
    }

    private boolean isImm12(int imm) {
        return imm >= -2048 && imm <= 2047;
    }

    /**
     * Check whether an expression contains any function call.
     */
    private boolean exprContainsCall(Expr expr) {
        return switch (expr) {
            case CallExpr ce -> true;
            case BinaryExpr be -> exprContainsCall(be.left()) || exprContainsCall(be.right());
            case UnaryExpr ue -> exprContainsCall(ue.operand());
            default -> false;
        };
    }

    /**
     * Check whether a statement assigns to a given variable name.
     */
    private boolean stmtAssignsTo(Stmt stmt, String name) {
        return switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts())
                    if (stmtAssignsTo(s, name)) yield true;
                yield false;
            }
            case AssignStmt as_ -> as_.name().equals(name);
            case IfStmt is -> stmtAssignsTo(is.thenStmt(), name)
                    || (is.elseStmt() != null && stmtAssignsTo(is.elseStmt(), name));
            case WhileStmt ws -> stmtAssignsTo(ws.body(), name);
            default -> false;
        };
    }

    /**
     * Check whether a statement contains any function call.
     */
    private boolean stmtContainsCall(Stmt stmt) {
        return switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts())
                    if (stmtContainsCall(s)) yield true;
                yield false;
            }
            case ExprStmt es -> exprContainsCall(es.expr());
            case AssignStmt as_ -> exprContainsCall(as_.value());
            case VarDecl vd -> exprContainsCall(vd.initExpr());
            case ConstDecl cd -> exprContainsCall(cd.initExpr());
            case IfStmt is -> exprContainsCall(is.condition())
                    || stmtContainsCall(is.thenStmt())
                    || (is.elseStmt() != null && stmtContainsCall(is.elseStmt()));
            case WhileStmt ws -> exprContainsCall(ws.condition())
                    || stmtContainsCall(ws.body());
            case ReturnStmt rs -> rs.value() != null && exprContainsCall(rs.value());
            default -> false;
        };
    }

    private String genLogicalAnd(BinaryExpr be) {
        // Short-circuit: if left is false, result is 0; else evaluate right
        String skipLabel = newLabel("and_skip");
        String endLabel = newLabel("and_end");

        String leftReg = genExpr(be.left());
        String resultReg = allocReg();

        // If left is 0 (false), result is 0 and skip right
        emit("mv", resultReg, leftReg);
        emit("beqz", leftReg, skipLabel);
        freeReg(leftReg);

        // Left was true: result = right != 0
        String rightReg = genExpr(be.right());
        emit("snez", resultReg, rightReg);
        freeReg(rightReg);
        emit("j", endLabel);

        // Left was false: result is already 0
        emitLabel(skipLabel);
        emitLabel(endLabel);

        return resultReg;
    }

    private String genLogicalOr(BinaryExpr be) {
        // Short-circuit: if left is true, result is 1; else evaluate right
        String skipLabel = newLabel("or_skip");
        String endLabel = newLabel("or_end");

        String leftReg = genExpr(be.left());
        String resultReg = allocReg();

        // If left is non-zero (true), result is 1 and skip right
        emit("snez", resultReg, leftReg);
        emit("bnez", leftReg, skipLabel);
        freeReg(leftReg);

        // Left was false: result = right != 0
        String rightReg = genExpr(be.right());
        emit("snez", resultReg, rightReg);
        freeReg(rightReg);
        emit("j", endLabel);

        // Left was true: result is already 1
        emitLabel(skipLabel);
        emitLabel(endLabel);

        return resultReg;
    }

    private String genUnary(UnaryExpr ue) {
        String operandReg = genExpr(ue.operand());
        String resultReg = allocReg();

        switch (ue.op()) {
            case "+" -> emit("mv", resultReg, operandReg);
            case "-" -> emit("sub", resultReg, "zero", operandReg);
            case "!" -> emit("seqz", resultReg, operandReg);
            default -> emit("mv", resultReg, operandReg);
        }
        freeReg(operandReg);
        return resultReg;
    }

    private String genCall(CallExpr ce) {
        // Before a call, clear last-store tracking since caller-saved regs
        // (t0-t6, a0-a7) will be clobbered. Must also free the underlying
        // temp registers, otherwise they stay marked as "used" forever.
        if (optimize) {
            for (String reg : lastStoreReg.values()) {
                freeRegRaw(reg);
            }
            invalidateRegCache();
            lastStoreReg.clear();
            regValid.clear();
            for (int i = 0; i < NUM_A_REGS; i++) aUsed[i] = false;
        }

        int numArgs = ce.args().size();
        int regArgCount = Math.min(numArgs, 8);
        int extraArgs = numArgs - 8;

        // Precompute which args contain function calls, so we can spill
        // live arg registers before a nested call clobbers t0-t6.
        boolean[] argHasCall = new boolean[numArgs];
        for (int i = 0; i < numArgs; i++) {
            argHasCall[i] = exprContainsCall(ce.args().get(i));
        }

        // Evaluate ALL args (both register and extra) into temp registers
        // or spill slots. Extra args are evaluated here (before register
        // args move to a0-a7) so nested calls inside extra args don't
        // clobber a0-a7.
        String[] argRegs = new String[numArgs];
        int[] argSpills = new int[numArgs]; // -1 = not spilled

        for (int i = 0; i < numArgs; i++) {
            argSpills[i] = -1;

            // If this arg contains a function call, spill all previously
            // evaluated live arg registers. Nested calls clobber t0-t6
            // (caller-saved), so any live value in a temp register will
            // be silently corrupted.
            if (argHasCall[i]) {
                for (int j = 0; j < i; j++) {
                    if (argRegs[j] != null && argSpills[j] == -1) {
                        argSpills[j] = allocateSpillSlot();
                        spillReg(argRegs[j], argSpills[j]);
                        freeReg(argRegs[j]);
                        argRegs[j] = null;
                    }
                }
            }

            // Ensure at least 2 free registers before evaluating each arg.
            // Binary expressions need 2 registers (left + right operand),
            // and complex expressions may need more. Spill the oldest live
            // (non-spilled) arg to free one up.
            while (countFreeRegs() < 2) {
                boolean spilled = false;
                for (int j = 0; j < i; j++) {
                    if (argRegs[j] != null && argSpills[j] == -1) {
                        argSpills[j] = allocateSpillSlot();
                        spillReg(argRegs[j], argSpills[j]);
                        freeReg(argRegs[j]);
                        argRegs[j] = null;
                        spilled = true;
                        break;
                    }
                }
                if (!spilled) break;
            }

            String r = genExpr(ce.args().get(i));
            argRegs[i] = r;
        }

        // Load back spilled register args directly into a-regs.
        // This avoids register exhaustion when all temp registers are
        // occupied by other non-spilled evaluated args.
        for (int i = 0; i < regArgCount; i++) {
            if (argSpills[i] != -1) {
                emit("lw", "a" + i, argSpills[i] + "(s0)");
                freeSpillSlot(argSpills[i]);
                argSpills[i] = -1;
                // arg temp reg was freed when spilled; mark as moved
                if (argRegs[i] != null) {
                    freeReg(argRegs[i]);
                }
                argRegs[i] = null;
            }
        }

        // Move non-spilled register args from temp regs to a-regs
        for (int i = 0; i < regArgCount; i++) {
            if (argRegs[i] != null) {
                emit("mv", "a" + i, argRegs[i]);
                freeReg(argRegs[i]);
                argRegs[i] = null;
            }
        }
        // At this point all temp registers should be free.

        // Load back spilled extra args (plenty of free regs now)
        for (int i = 8; i < numArgs; i++) {
            if (argSpills[i] != -1) {
                argRegs[i] = loadSpill(argSpills[i]);
                freeSpillSlot(argSpills[i]);
                argSpills[i] = -1;
            }
        }

        // Set up outgoing-arg area on stack for args beyond 8
        int extraAlignedSize = 0;
        if (extraArgs > 0) {
            int extraSize = extraArgs * 4;
            extraAlignedSize = (extraSize + 15) & ~15;
            emit("addi", "sp", "sp", String.valueOf(-extraAlignedSize));

            for (int i = 8; i < numArgs; i++) {
                if (argRegs[i] != null) {
                    int offset = (i - 8) * 4;
                    emit("sw", argRegs[i], offset + "(sp)");
                    freeReg(argRegs[i]);
                    argRegs[i] = null;
                }
            }
        }

        // Call the function
        emit("call", ce.funcName());

        // Deallocate extra-args space
        if (extraAlignedSize > 0) {
            emit("addi", "sp", "sp", String.valueOf(extraAlignedSize));
        }

        // Result is in a0, move to a temp register
        String resultReg = allocReg();
        emit("mv", resultReg, "a0");
        return resultReg;
    }

    /** Count the number of free (unused) temp registers. */
    private int countFreeRegs() {
        int count = 0;
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (!tempUsed[i]) count++;
        }
        return count;
    }

    // ========== Optimization helpers ==========

    /** Check if expression is pure (no side effects, no function calls). */
    private boolean isPureExpr(Expr expr) {
        return switch (expr) {
            case LiteralExpr le -> true;
            case IdExpr id -> true;
            case BinaryExpr be -> isPureExpr(be.left()) && isPureExpr(be.right());
            case UnaryExpr ue -> isPureExpr(ue.operand());
            case CallExpr ce -> false; // function calls may have side effects
        };
    }

    /** Check if expression has side effects (contains function calls). */
    private boolean hasSideEffects(Expr expr) {
        return !isPureExpr(expr);
    }

    /** Check if a variable name is used (read) in a given statement subtree. */
    private boolean isVarUsed(String name, Stmt stmt) {
        return switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts())
                    if (isVarUsed(name, s)) yield true;
                yield false;
            }
            case ExprStmt es -> exprUsesVar(name, es.expr());
            case AssignStmt as_ -> as_.name().equals(name) || exprUsesVar(name, as_.value());
            case VarDecl vd -> exprUsesVar(name, vd.initExpr());
            case ConstDecl cd -> exprUsesVar(name, cd.initExpr());
            case IfStmt is -> exprUsesVar(name, is.condition())
                    || isVarUsed(name, is.thenStmt())
                    || (is.elseStmt() != null && isVarUsed(name, is.elseStmt()));
            case WhileStmt ws -> exprUsesVar(name, ws.condition())
                    || isVarUsed(name, ws.body());
            case ReturnStmt rs -> rs.value() != null && exprUsesVar(name, rs.value());
            default -> false;
        };
    }

    /** Check if an expression references a variable name. */
    private boolean exprUsesVar(String name, Expr expr) {
        return switch (expr) {
            case IdExpr id -> id.name().equals(name);
            case BinaryExpr be -> exprUsesVar(name, be.left()) || exprUsesVar(name, be.right());
            case UnaryExpr ue -> exprUsesVar(name, ue.operand());
            case CallExpr ce -> {
                for (Expr arg : ce.args())
                    if (exprUsesVar(name, arg)) yield true;
                yield false;
            }
            default -> false;
        };
    }

    // ========== Register allocation ==========

    private String allocReg() {
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (!tempUsed[i]) {
                tempUsed[i] = true;
                // This register is being reused — any last-store value is gone
                regValid.remove(TEMP_REGS[i]);
                return TEMP_REGS[i];
            }
        }
        // All temp registers are in use. Try to steal one from the
        // last-store cache (optimization). These registers hold values
        // already stored to memory, so stealing them is safe — the
        // next read will just use lw instead.
        if (optimize) {
            for (int i = 0; i < NUM_TEMPS; i++) {
                String reg = TEMP_REGS[i];
                if (regValid.contains(reg)) {
                    // Find which variable this register was cached for
                    String varName = null;
                    for (var e : lastStoreReg.entrySet()) {
                        if (e.getValue().equals(reg)) {
                            varName = e.getKey();
                            break;
                        }
                    }
                    if (varName != null) {
                        lastStoreReg.remove(varName);
                    }
                    regValid.remove(reg);
                    tempUsed[i] = true;
                    return reg;
                }
            }
            // Try to evict a clean cached variable from the register cache.
            for (String varName : new ArrayList<>(varRegCache.keySet())) {
                if (!varDirty.contains(varName)) {
                    String reg = varRegCache.get(varName);
                    if (reg != null) {
                        varRegCache.remove(varName);
                        regToVar.remove(reg);
                        tempUsed[regIndex(reg)] = true;
                        return reg;
                    }
                }
            }
            // All cached vars are dirty — flush one then evict.
            if (!varRegCache.isEmpty()) {
                String varName = varRegCache.keySet().iterator().next();
                invalidateVar(varName);
                return allocReg();
            }
        }
        // Overflow: use a0-a7 as additional temp registers.
        for (int i = 0; i < NUM_A_REGS; i++) {
            if (!aUsed[i]) { aUsed[i] = true; return A_REGS[i]; }
        }
        throw new RuntimeException("out of temporary registers");
    }

    /** Get the index of a temp register (0-6). */
    private int regIndex(String reg) {
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) return i;
        }
        return -1;
    }

    private boolean hasFreeReg() {
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (!tempUsed[i]) return true;
        }
        return false;
    }

    private void freeReg(String reg) {
        if (reg.startsWith("a")) {
            for (int i = 0; i < NUM_A_REGS; i++)
                if (A_REGS[i].equals(reg)) { aUsed[i] = false; return; }
            return;
        }
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) {
                tempUsed[i] = false;
                regValid.remove(reg);
                if (optimize) {
                    String var = regToVar.remove(reg);
                    if (var != null) { varRegCache.remove(var); varDirty.remove(var); }
                }
                return;
            }
        }
    }

    /** Free a temp register without touching the cache. */
    private void freeRegRaw(String reg) {
        if (reg.startsWith("a")) {
            for (int i = 0; i < NUM_A_REGS; i++)
                if (A_REGS[i].equals(reg)) { aUsed[i] = false; return; }
            return;
        }
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) { tempUsed[i] = false; return; }
        }
    }

    // Spill slot for preserving register across right-operand evaluation.
    // Uses a frame-relative slot (s0-relative) to avoid sp alignment issues
    // and function call clobbering of temp registers.
    // Slots are recycled via a free stack so max live spill depth bounds frame usage.
    private int nextSpillOffset = 0; // will be set during genFuncDef
    private final Deque<Integer> freeSpillSlots = new ArrayDeque<>();

    private int allocateSpillSlot() {
        if (!freeSpillSlots.isEmpty()) {
            return freeSpillSlots.pop();
        }
        int slot = nextSpillOffset;
        nextSpillOffset -= 4;
        return slot;
    }

    private void freeSpillSlot(int offset) {
        freeSpillSlots.push(offset);
    }

    private void spillReg(String reg, int offset) {
        emit("sw", reg, offset + "(s0)");
    }

    private String loadSpill(int offset) {
        String reg = allocReg();
        emit("lw", reg, offset + "(s0)");
        return reg;
    }

    // ========== Helpers ==========

    private String newLabel(String prefix) {
        return ".L." + prefix + "." + (labelCounter++);
    }

    private void emitLabel(String label) {
        sb.append(label).append(":\n");
    }

    private void emit(String instr) {
        sb.append("  ").append(instr).append("\n");
    }

    private void emit(String instr, String operand) {
        sb.append("  ").append(instr).append(" ").append(operand).append("\n");
    }

    private void emit(String instr, String op1, String op2) {
        sb.append("  ").append(instr).append(" ").append(op1)
                .append(", ").append(op2).append("\n");
    }

    private void emit(String instr, String op1, String op2, String op3) {
        sb.append("  ").append(instr).append(" ").append(op1)
                .append(", ").append(op2).append(", ").append(op3).append("\n");
    }
}
