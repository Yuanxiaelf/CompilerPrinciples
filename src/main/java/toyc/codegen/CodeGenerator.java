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

    // Registers for expression evaluation.
    // Seven caller-saved t-registers are always available as scratch.
    private static final String[] TEMP_REGS = {"t0", "t1", "t2", "t3", "t4", "t5", "t6"};
    private static final int NUM_TEMPS = 7;
    private final boolean[] tempUsed = new boolean[NUM_TEMPS];

    // S-registers available for persistent variable caching (callee-saved).
    // s0 is already used as frame pointer; s1-s11 are free.
    private static final String[] S_REGS = {
        "s1","s2","s3","s4","s5","s6","s7","s8","s9","s10","s11"
    };
    private static final int NUM_S_REGS = 11;

    // Variable-to-s-register mapping for the current function.
    private final Map<String, String> varToSReg = new HashMap<>();
    private final Map<String, String> sRegToVar = new HashMap<>();
    private final Set<String> sRegDirty = new HashSet<>(); // s-regs needing writeback
    // Which s-registers are actually used in the current function (for save/restore).
    private final Set<String> usedSRegs = new LinkedHashSet<>();
    // Stack offsets where s-regs are saved in frame (assigned during prologue).
    private final Map<String, Integer> sRegSaveOffset = new HashMap<>();

    // Current function context
    private FuncDef currentFunc;
    private boolean currentFuncIsLeaf;
    private final Deque<Map<String, Integer>> localOffsetStack = new ArrayDeque<>(); // scoped variable → offset from fp
    private int nextLocalOffset; // grows downward (negative)

    // Frame info
    private int frameSize;

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
        varToSReg.clear();
        sRegToVar.clear();
        sRegDirty.clear();
        usedSRegs.clear();
        sRegSaveOffset.clear();

        // Determine whether this is a leaf function (no calls in body)
        boolean isLeaf = !stmtContainsCall(fd.body());
        currentFuncIsLeaf = isLeaf;

        Symbol funcSym = analyzer.getFuncSymbols().get(fd);

        // ---- Variable-to-s-register assignment (optimization) ----
        // Must happen BEFORE countLocals because s-reg saves affect
        // the local offset starting point.
        if (optimize) {
            Map<String, Integer> varUseCounts = new HashMap<>();
            countVarReads(fd.body(), varUseCounts);

            // Also count parameters.
            if (funcSym != null && funcSym.getFuncParamNames() != null) {
                for (String pn : funcSym.getFuncParamNames()) {
                    varUseCounts.putIfAbsent(pn, 0);
                    varUseCounts.put(pn, varUseCounts.get(pn) + 1);
                }
            }

            List<String> sortedVars = varUseCounts.entrySet().stream()
                .filter(e -> e.getValue() >= 2) // only cache if used 2+ times
                .sorted(Map.Entry.<String, Integer>comparingByValue().reversed())
                .map(Map.Entry::getKey)
                .toList();

            int sIdx = 0;
            for (String varName : sortedVars) {
                if (sIdx >= NUM_S_REGS) break;
                String sReg = S_REGS[sIdx];
                varToSReg.put(varName, sReg);
                sRegToVar.put(sReg, varName);
                usedSRegs.add(sReg);
                sIdx++;
            }
        }

        // s-reg saves go below ra/s0 save slots.
        // nextLocalOffset must start past ra, s0, AND all s-reg saves.
        int sRegSaveCount = usedSRegs.size();
        nextLocalOffset = -8 - sRegSaveCount * 4;

        // Count locals declared in the body
        countLocals(fd.body());

        boolean leafParamsKeptInRegs = false;
        if (isLeaf && funcSym != null && funcSym.getFuncParamNames() != null) {
            leafParamsKeptInRegs = true;
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

        // Save the final offset for frame calculation.
        int finalLocalOffset = nextLocalOffset;

        // Reserve spill slots for expression evaluation.
        int maxSpillDepth = calcMaxSpillDepth(fd.body());
        if (!isLeaf) {
            // Nested calls can cause cascading spills in genCall's arg loop.
            maxSpillDepth += 12;
        }
        int spillAreaSize = maxSpillDepth * 4;

        boolean hasLocalsOrParams = finalLocalOffset < -(8 + sRegSaveCount * 4);
        boolean needsFrame = hasLocalsOrParams || maxSpillDepth > 0;

        // Calculate frame size — include space for saved s-registers.
        int savedRegsSize = (needsFrame || !isLeaf) ? 8 : 0; // ra + s0
        int sRegSaveSize = sRegSaveCount * 4;

        int baseOffset = 8 + sRegSaveSize;
        int localSize = -finalLocalOffset - baseOffset;
        if (localSize < 0) localSize = 0;
        frameSize = savedRegsSize + sRegSaveSize + localSize + spillAreaSize;
        frameSize = (frameSize + 15) & ~15; // 16-byte aligned

        // Assign save slots for s-registers in the frame.
        // Layout (high to low): ra, s0, s1, s2, ..., locals, spills
        {
            int sOffset = frameSize - 8 - 4; // start below s0 save slot
            for (String sr : usedSRegs) {
                sRegSaveOffset.put(sr, sOffset);
                sOffset -= 4;
            }
        }

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
            // Save used s-registers
            for (String sr : usedSRegs) {
                int off = sRegSaveOffset.get(sr);
                emit("sw", sr, off + "(sp)");
            }
            emit("addi", "s0", "sp", String.valueOf(frameSize));
        }

        // Reset local offset state for code generation.
        // Start past ra(-4), s0(-8), and s-reg saves.
        nextLocalOffset = -8 - sRegSaveCount * 4;
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
        // Also initialize s-register values for params assigned to s-regs.
        if (!leafParamsKeptInRegs && funcSym != null
                && funcSym.getFuncParamNames() != null && frameSize > 0) {
            int argReg = 0;
            for (String paramName : funcSym.getFuncParamNames()) {
                if (argReg < 8) {
                    String aReg = "a" + argReg;
                    int offset = getLocalOffset(paramName);
                    emit("sw", aReg, offset + "(s0)");
                    // If this param is cached in an s-reg, load it now.
                    String sReg = varToSReg.get(paramName);
                    if (sReg != null) {
                        emit("mv", sReg, aReg);
                        sRegDirty.add(sReg);
                    }
                }
                argReg++;
            }
        }

        // Generate body
        genStmt(fd.body());

        // Epilogue — write back dirty s-regs before exit.
        emitLabel(funcEpilogueLabel());
        flushAllSRegDirty();
        if (frameSize > 0) {
            // Restore s-registers
            for (String sr : usedSRegs) {
                int off = sRegSaveOffset.get(sr);
                emit("lw", sr, off + "(sp)");
            }
            if (!isLeaf) {
                emit("lw", "ra", (frameSize - 4) + "(sp)");
            }
            emit("lw", "s0", (frameSize - 8) + "(sp)");
            emit("addi", "sp", "sp", String.valueOf(frameSize));
        }
        emit("ret");

        currentFunc = null;
    }

    /** Count variable reads in a statement subtree. */
    private void countVarReads(Stmt stmt, Map<String, Integer> counts) {
        switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) countVarReads(s, counts);
            }
            case ExprStmt es -> countExprReads(es.expr(), counts);
            case AssignStmt as_ -> {
                countExprReads(as_.value(), counts);
                // Don't count the assign target as a "read"
            }
            case VarDecl vd -> countExprReads(vd.initExpr(), counts);
            case ConstDecl cd -> countExprReads(cd.initExpr(), counts);
            case IfStmt is -> {
                countExprReads(is.condition(), counts);
                countVarReads(is.thenStmt(), counts);
                if (is.elseStmt() != null) countVarReads(is.elseStmt(), counts);
            }
            case WhileStmt ws -> {
                countExprReads(ws.condition(), counts);
                countVarReads(ws.body(), counts);
            }
            case ReturnStmt rs -> {
                if (rs.value() != null) countExprReads(rs.value(), counts);
            }
            default -> {}
        }
    }

    /** Count variable reads in an expression. */
    private void countExprReads(Expr expr, Map<String, Integer> counts) {
        switch (expr) {
            case IdExpr id -> counts.merge(id.name(), 1, Integer::sum);
            case BinaryExpr be -> {
                countExprReads(be.left(), counts);
                countExprReads(be.right(), counts);
            }
            case UnaryExpr ue -> countExprReads(ue.operand(), counts);
            case CallExpr ce -> {
                for (Expr arg : ce.args()) countExprReads(arg, counts);
            }
            default -> {}
        }
    }

    /** Write back all dirty s-register variables to their stack slots. */
    private void flushAllSRegDirty() {
        if (!optimize) return;
        for (String varName : new ArrayList<>(sRegDirty)) {
            String sReg = varToSReg.get(varName);
            if (sReg == null) continue;
            Integer off = lookupLocalOffset(varName);
            if (off != null) {
                emit("sw", sReg, off + "(s0)");
            }
        }
        sRegDirty.clear();
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
                // before evaluating call-containing args. Worst case:
                // all register args (up to 8) spilled PLUS max arg depth
                // for nested call evaluations. Use sum to be conservative.
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
                String r = genExpr(as_.value());
                // Check local scope first (handles shadowing of globals)
                Integer localOff = lookupLocalOffset(as_.name());
                if (localOff != null) {
                    // S-register caching: update the s-register value too.
                    if (optimize) {
                        String sReg = varToSReg.get(as_.name());
                        if (sReg != null) {
                            emit("mv", sReg, r);
                            sRegDirty.add(sReg);
                        }
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
                            String sReg = varToSReg.get(as_.name());
                            if (sReg != null) {
                                emit("mv", sReg, r);
                                sRegDirty.add(sReg);
                            }
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
                String r = genExpr(vd.initExpr());
                int offset = allocateLocal(vd.name());
                // S-register caching for the new variable.
                if (optimize) {
                    String sReg = varToSReg.get(vd.name());
                    if (sReg != null) {
                        emit("mv", sReg, r);
                        sRegDirty.add(sReg);
                    }
                    if (enableRegCache) {
                        cacheVar(vd.name(), r);
                        varDirty.remove(vd.name());
                    }
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
                // S-register caching for the new constant.
                if (optimize) {
                    String sReg = varToSReg.get(cd.name());
                    if (sReg != null) {
                        emit("mv", sReg, r);
                        sRegDirty.add(sReg);
                    }
                }
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
        flushAllSRegDirty();
        if (rs.value() != null) {
            String r = genExpr(rs.value());
            emit("mv", "a0", r); // return value in a0
            freeReg(r);
        }
        // Jump to epilogue
        emit("j", funcEpilogueLabel());
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

        // S-register variable cache: if this variable lives in an s-register,
        // just copy its value to a temp register (or alloc it directly).
        if (optimize) {
            String sReg = varToSReg.get(id.name());
            if (sReg != null) {
                // Variable is cached in an s-register — no lw needed.
                String r = allocReg();
                emit("mv", r, sReg);
                return r;
            }
        }

        // Last-store optimization: if variable was just stored and its
        // register hasn't been reused, use it directly (avoid lw).
        if (optimize) {
            String lsReg = lastStoreReg.get(id.name());
            if (lsReg != null && regValid.contains(lsReg)) {
                // Register still holds the value — use it and consume.
                regValid.remove(lsReg);
                lastStoreReg.remove(id.name());
                // Mark this register as allocated for the caller.
                tempUsed[regIndex(lsReg)] = true;
                return lsReg;
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
            Symbol funcSym = analyzer.getFuncSymbols().get(currentFunc);
            int paramIdx = -1;
            if (funcSym != null && funcSym.getFuncParamNames() != null) {
                paramIdx = funcSym.getFuncParamNames().indexOf(id.name());
            }
            if (paramIdx >= 0 && paramIdx < 8) {
                emit("mv", r, "a" + paramIdx);
            } else {
                emit("li", r, "0"); // fallback (should not happen)
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

        // Optimization: if right operand is a simple literal and the
        // operation can use an immediate form, skip evaluating the right
        // operand into a register entirely. This avoids dead li instructions.
        if (optimize && be.right() instanceof LiteralExpr rle
                && !exprContainsCall(be.left())) {
            int imm = rle.value();
            String resultReg = genExpr(be.left());

            // Try algebraic identities first
            boolean handled = false;
            switch (be.op()) {
                case "+" -> { if (imm == 0) handled = true; }
                case "-" -> { if (imm == 0) handled = true; }
                case "*" -> {
                    if (imm == 0) { emit("mv", resultReg, "zero"); handled = true; }
                    else if (imm == 1) handled = true;
                    else if ((imm & (imm - 1)) == 0) {
                        int shift = Integer.numberOfTrailingZeros(imm);
                        emit("slli", resultReg, resultReg, String.valueOf(shift));
                        handled = true;
                    }
                }
                case "/" -> { if (imm == 1) handled = true; }
                case "%" -> {
                    if (imm == 1) { emit("mv", resultReg, "zero"); handled = true; }
                    else if ((imm & (imm - 1)) == 0) {
                        emit("andi", resultReg, resultReg, String.valueOf(imm - 1));
                        handled = true;
                    }
                }
            }
            if (handled) return resultReg;

            // Try immediate-form instruction
            if (tryEmitImmOp(be.op(), resultReg, resultReg, imm))
                return resultReg;

            // Fall through: need a register for the literal after all.
            // But we already evaluated left — allocate right and proceed.
            String rightReg = allocReg();
            emit("li", rightReg, String.valueOf(imm));
            emitBinaryOp(be.op(), resultReg, resultReg, rightReg);
            freeReg(rightReg);
            return resultReg;
        }

        // ---- General case: evaluate both operands ----

        String leftReg = genExpr(be.left());

        // Only spill left if the right operand contains a function call
        String rightReg;
        String resultReg;

        if (exprContainsCall(be.right())) {
            int spillOffset = allocateSpillSlot();
            spillReg(leftReg, spillOffset);
            freeReg(leftReg);

            rightReg = genExpr(be.right());
            resultReg = loadSpill(spillOffset);
            freeSpillSlot(spillOffset);
        } else {
            rightReg = genExpr(be.right());
            resultReg = leftReg;
        }

        // Strength reduction: use immediate instructions when possible
        if (optimize && be.right() instanceof LiteralExpr rle) {
            int imm = rle.value();
            switch (be.op()) {
                case "+" -> {
                    if (imm == 0) { freeReg(rightReg); return resultReg; }
                }
                case "-" -> {
                    if (imm == 0) { freeReg(rightReg); return resultReg; }
                }
                case "*" -> {
                    if (imm == 0) {
                        emit("mv", resultReg, "zero");
                        freeReg(rightReg); return resultReg;
                    }
                    if (imm == 1) { freeReg(rightReg); return resultReg; }
                    if ((imm & (imm - 1)) == 0) {
                        int shift = Integer.numberOfTrailingZeros(imm);
                        emit("slli", resultReg, resultReg, String.valueOf(shift));
                        freeReg(rightReg);
                        return resultReg;
                    }
                }
                case "/" -> {
                    if (imm == 1) { freeReg(rightReg); return resultReg; }
                }
                case "%" -> {
                    if (imm == 1) {
                        emit("mv", resultReg, "zero");
                        freeReg(rightReg); return resultReg;
                    }
                    if ((imm & (imm - 1)) == 0) {
                        emit("andi", resultReg, resultReg, String.valueOf(imm - 1));
                        freeReg(rightReg);
                        return resultReg;
                    }
                }
            }
            if (tryEmitImmOp(be.op(), resultReg, resultReg, imm)) {
                freeReg(rightReg);
                return resultReg;
            }
        }

        // Commutative left-literal folding: 0 + x → x, 1 * x → x, etc.
        if (optimize && be.left() instanceof LiteralExpr lle) {
            int imm = lle.value();
            switch (be.op()) {
                case "+" -> {
                    if (imm == 0) {
                        freeReg(leftReg);
                        return rightReg;
                    }
                }
                case "*" -> {
                    if (imm == 0) {
                        emit("mv", resultReg, "zero");
                        freeReg(rightReg);
                        return resultReg;
                    }
                    if (imm == 1) {
                        freeReg(leftReg);
                        return rightReg;
                    }
                }
                case "-" -> {
                    if (imm == 0) {
                        emit("sub", resultReg, "zero", rightReg);
                        freeReg(rightReg);
                        return resultReg;
                    }
                }
            }
        }

        emitBinaryOp(be.op(), resultReg, resultReg, rightReg);
        freeReg(rightReg);
        return resultReg;
    }

    /** Emit a binary operation with two register operands. */
    private void emitBinaryOp(String op, String rd, String rs1, String rs2) {
        switch (op) {
            case "+" -> emit("add", rd, rs1, rs2);
            case "-" -> emit("sub", rd, rs1, rs2);
            case "*" -> emit("mul", rd, rs1, rs2);
            case "/" -> emit("div", rd, rs1, rs2);
            case "%" -> emit("rem", rd, rs1, rs2);
            case "==" -> {
                emit("sub", rd, rs1, rs2);
                emit("seqz", rd, rd);
            }
            case "!=" -> {
                emit("sub", rd, rs1, rs2);
                emit("snez", rd, rd);
            }
            case "<"  -> emit("slt", rd, rs1, rs2);
            case ">=" -> {
                emit("slt", rd, rs1, rs2);
                emit("xori", rd, rd, "1");
            }
            case ">"  -> emit("slt", rd, rs2, rs1);
            case "<=" -> {
                emit("slt", rd, rs2, rs1);
                emit("xori", rd, rd, "1");
            }
            default -> emit("add", rd, rs1, rs2);
        }
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
        if (imm < -2048 || imm > 2047) return false;
        switch (op) {
            case "+" -> { emit("addi", rd, rs, String.valueOf(imm)); return true; }
            case "-" -> { emit("addi", rd, rs, String.valueOf(-imm)); return true; }
            case "<" -> { emit("slti", rd, rs, String.valueOf(imm)); return true; }
            case ">=" -> {
                emit("slti", rd, rs, String.valueOf(imm));
                emit("xori", rd, rd, "1");
                return true;
            }
            case ">" -> {
                // rs > imm  ≡  imm < rs  ≡  slti rd, rs, imm+1  ...
                // Actually: a > b  ≡  b < a. For constant b:
                // rs > imm  ≡  imm < rs  ≡  imm+1 <= rs  ≡  slti rd, rs, imm+1 then xori
                // Simpler: rs > imm  ≡  rs >= imm+1  ≡  NOT(rs < imm+1)  ≡  slti rd,rs,imm+1; xori rd,rd,1
                if (imm < 2047) {
                    emit("slti", rd, rs, String.valueOf(imm + 1));
                    emit("xori", rd, rd, "1");
                    return true;
                }
                // imm == 2047: rs > 2047  ≡  rs >= 2048 (out of 12-bit range) → fall back
                return false;
            }
            case "<=" -> {
                // rs <= imm  ≡  NOT(imm < rs)  ≡  NOT(rs > imm)  ≡  slti rd,rs,imm+1 but inverted...
                // a <= b  ≡  NOT(b < a). For constant: rs <= imm  ≡  NOT(imm < rs)
                // slt rd, zero, rs  → if rs > 0 then 1... hmm.
                // Better: rs <= imm  ≡  rs < imm+1  ≡  slti rd, rs, imm+1
                if (imm < 2047) {
                    emit("slti", rd, rs, String.valueOf(imm + 1));
                    return true;
                }
                return false;
            }
            case "==" -> {
                if (imm == 0) {
                    emit("seqz", rd, rs);
                } else {
                    emit("addi", rd, rs, String.valueOf(-imm));
                    emit("seqz", rd, rd);
                }
                return true;
            }
            case "!=" -> {
                if (imm == 0) {
                    emit("snez", rd, rs);
                } else {
                    emit("addi", rd, rs, String.valueOf(-imm));
                    emit("snez", rd, rd);
                }
                return true;
            }
            default -> { return false; }
        }
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
        // Before a call: flush s-register dirty bits to stack for safety
        // (callee-saved s-regs survive the call, but we want the stack
        // to reflect the latest values in case of recursion etc.).
        if (optimize) {
            flushAllSRegDirty();
        }

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

            // Last resort: evict a dirty s-register variable.
            // Write it back to its stack slot and reuse the s-reg as a temp.
            if (!sRegDirty.isEmpty()) {
                String varName = sRegDirty.iterator().next();
                String sReg = varToSReg.get(varName);
                if (sReg != null) {
                    Integer off = lookupLocalOffset(varName);
                    if (off != null) {
                        emit("sw", sReg, off + "(s0)");
                    }
                    sRegDirty.remove(varName);
                    // Remove from cache so future reads hit the stack.
                    varToSReg.remove(varName);
                    sRegToVar.remove(sReg);
                    return sReg;
                }
            }
            // If we have any clean s-reg variable, steal its register.
            for (var e : varToSReg.entrySet()) {
                if (!sRegDirty.contains(e.getKey())) {
                    String sReg = e.getValue();
                    varToSReg.remove(e.getKey());
                    sRegToVar.remove(sReg);
                    return sReg;
                }
            }
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
        // Handle s-registers that were stolen as temps.
        if (reg.startsWith("s")) {
            // This was an s-register used as a temp. Just return — it's
            // not tracked in tempUsed, and its original variable mapping
            // was already cleared when stolen.
            return;
        }
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) {
                tempUsed[i] = false;
                // This register is being freed — any last-store value is gone
                regValid.remove(reg);
                // If this register was cached for a variable, invalidate
                if (optimize) {
                    String var = regToVar.remove(reg);
                    if (var != null) {
                        varRegCache.remove(var);
                        varDirty.remove(var);
                    }
                }
                return;
            }
        }
    }

    /** Free a temp register without touching the cache. */
    private void freeRegRaw(String reg) {
        // s-registers are not tracked in tempUsed.
        if (reg.startsWith("s")) return;
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) {
                tempUsed[i] = false;
                return;
            }
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
