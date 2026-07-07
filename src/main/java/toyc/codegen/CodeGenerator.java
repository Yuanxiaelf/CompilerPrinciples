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
    // Register cache: keep local variables in registers to reduce memory traffic.
    // Requires proper invalidation before function calls (invalidateRegCache)
    // and stable register assignment across loop iterations.
    private static final boolean enableRegCache = true;
    private final StringBuilder sb;
    private int labelCounter;
    private final Deque<LoopLabels> loopStack;

    // Registers for expression evaluation
    private static final String[] TEMP_REGS = {"t0", "t1", "t2", "t3", "t4", "t5", "t6"};
    private static final int NUM_TEMPS = 7;
    private final boolean[] tempUsed = new boolean[NUM_TEMPS];

    // Current function context
    private FuncDef currentFunc;
    private boolean currentFuncIsLeaf;
    private final Deque<Map<String, Integer>> localOffsetStack = new ArrayDeque<>(); // scoped variable → offset from fp
    private int nextLocalOffset; // grows downward (negative)

    // Frame info
    private int frameSize;

    // Register cache for local variables (optimization)
    // Maps variable name → register holding its current value
    private final Map<String, String> varRegCache = new HashMap<>();
    // Maps register → variable name (reverse mapping)
    private final Map<String, String> regToVar = new HashMap<>();
    // Tracks whether a cached variable has been stored to its stack slot
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
        nextLocalOffset = -8; // skip past saved ra (-4) and saved fp (-8)

        // Count locals declared in the body
        countLocals(fd.body());

        // Determine whether this is a leaf function (no calls in body)
        // and whether parameters can be kept in a0-a7 registers.
        boolean isLeaf = !stmtContainsCall(fd.body());
        currentFuncIsLeaf = isLeaf;

        Symbol funcSym = analyzer.getFuncSymbols().get(fd);
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

        // Save the final offset for frame calculation, then reset for code gen.
        // countLocals and getLocalOffset above advance nextLocalOffset but pop
        // block scopes, so genStmt must restart from -8 to produce matching offsets.
        int finalLocalOffset = nextLocalOffset;

        // Reserve spill slots for expression evaluation.
        int maxSpillDepth = calcMaxSpillDepth(fd.body());
        int spillAreaSize = maxSpillDepth * 4;

        boolean hasLocalsOrParams = finalLocalOffset < -8;
        boolean needsFrame = hasLocalsOrParams || maxSpillDepth > 0;

        // Calculate frame size.
        int savedRegsSize = (needsFrame || !isLeaf) ? 8 : 0;

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
        if (!leafParamsKeptInRegs && funcSym != null
                && funcSym.getFuncParamNames() != null && frameSize > 0) {
            int argReg = 0;
            for (String paramName : funcSym.getFuncParamNames()) {
                if (argReg < 8) {
                    String reg = "a" + argReg;
                    int offset = getLocalOffset(paramName);
                    emit("sw", reg, offset + "(s0)");
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
                yield maxD;
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
                // Flush and invalidate block-scoped variables on exit
                for (String name : blockVars) {
                    invalidateVar(name);
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
                if (!optimize || !enableRegCache) {
                    freeReg(r);
                }
                // With register cache enabled, register stays cached
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
                if (optimize && enableRegCache) {
                    cacheVar(vd.name(), r);
                    varDirty.remove(vd.name()); // stored below
                }
                emit("sw", r, offset + "(s0)");
                if (!optimize || !enableRegCache) {
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
                if (optimize && enableRegCache) {
                    cacheVar(cd.name(), r);
                    varDirty.remove(cd.name());
                }
                emit("sw", r, offset + "(s0)");
                if (!optimize || !enableRegCache) {
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

        // Optimization: check register cache first
        if (optimize) {
            String cachedReg = getCachedReg(id.name());
            if (cachedReg != null) {
                // Copy the cached value to a new register for this use.
                // The cached register stays owned by the cache.
                String r = allocReg();
                emit("mv", r, cachedReg);
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

        String leftReg = genExpr(be.left());

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

        // Strength reduction: use immediate instructions when possible
        if (optimize && be.right() instanceof LiteralExpr rle) {
            int imm = rle.value();
            if (tryEmitImmOp(be.op(), resultReg, resultReg, imm)) {
                freeReg(rightReg);
                return resultReg;
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
        // Before a call, flush register cache since caller-saved regs (t0-t6, a0-a7)
        // will be clobbered.
        if (optimize) {
            invalidateRegCache();
        }

        int numArgs = ce.args().size();

        // Phase 1: Evaluate all register args (0..min(numArgs,8)-1) into
        // temp registers. We accumulate them first so nested function calls
        // inside later args cannot clobber a0-a7 already set for earlier args.
        int regArgCount = Math.min(numArgs, 8);
        List<String> argRegs = new ArrayList<>();
        List<Integer> argSpillOffsets = new ArrayList<>();

        for (int i = 0; i < regArgCount; i++) {
            // If we're low on temp registers, spill the oldest accumulated
            // arg to a frame slot to free up a register.
            if (!hasFreeReg()) {
                // Find the first non-null (live) arg to spill
                int spillIdx = 0;
                while (spillIdx < argRegs.size() && argRegs.get(spillIdx) == null) {
                    spillIdx++;
                }
                if (spillIdx < argRegs.size()) {
                    int spillOff = allocateSpillSlot();
                    spillReg(argRegs.get(spillIdx), spillOff);
                    freeReg(argRegs.get(spillIdx));
                    argSpillOffsets.add(spillOff);
                    argRegs.set(spillIdx, null);
                }
            }
            String r = genExpr(ce.args().get(i));
            argRegs.add(r);
            argSpillOffsets.add(-1); // -1 means "not spilled"
        }

        // Phase 2a: Load all spilled args back from spill slots.
        // Track which args we move to a-regs early (to free up temp regs).
        int spillCursor = 0;
        Set<Integer> alreadyMoved = new HashSet<>();
        for (int i = 0; i < argRegs.size(); i++) {
            if (argRegs.get(i) == null) {
                // If no free register, move a later held arg to its a-reg
                // early to free up a temp register for loading the spill.
                if (!hasFreeReg()) {
                    for (int j = i + 1; j < argRegs.size(); j++) {
                        String rj = argRegs.get(j);
                        if (rj != null) {
                            emit("mv", "a" + j, rj);
                            freeReg(rj);
                            alreadyMoved.add(j);
                            break;
                        }
                    }
                }
                // Find spill offset for this spilled arg
                while (spillCursor < argSpillOffsets.size() &&
                       argSpillOffsets.get(spillCursor) == -1) {
                    spillCursor++;
                }
                int off = argSpillOffsets.get(spillCursor);
                String reg = loadSpill(off);
                freeSpillSlot(off);
                argRegs.set(i, reg);
                spillCursor++;
            }
        }

        // Phase 2b: Move remaining held args to a-regs
        for (int i = 0; i < argRegs.size(); i++) {
            if (!alreadyMoved.contains(i)) {
                String reg = argRegs.get(i);
                if (reg != null) {
                    emit("mv", "a" + i, reg);
                    freeReg(reg);
                }
            }
        }

        // Phase 3: Handle args beyond 8 — allocate outgoing-arg area below sp,
        // store args, then call.
        int extraArgs = numArgs - 8;
        int extraAlignedSize = 0;
        if (extraArgs > 0) {
            int extraSize = extraArgs * 4;
            extraAlignedSize = (extraSize + 15) & ~15;
            emit("addi", "sp", "sp", String.valueOf(-extraAlignedSize));

            for (int i = 8; i < numArgs; i++) {
                String r = genExpr(ce.args().get(i));
                int offset = (i - 8) * 4;
                emit("sw", r, offset + "(sp)");
                freeReg(r);
            }
        }

        // Phase 4: Call function
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
                return TEMP_REGS[i];
            }
        }
        // All temp registers are in use. If optimizing, evict a cached
        // (non-dirty) variable to free one. Dirty vars must stay for correctness.
        if (optimize) {
            // Copy key set to avoid ConcurrentModificationException
            for (String varName : new ArrayList<>(varRegCache.keySet())) {
                if (!varDirty.contains(varName)) {
                    // This var is clean (already stored to memory) — safe to evict.
                    String reg = varRegCache.get(varName);
                    if (reg != null) {
                        varRegCache.remove(varName);
                        regToVar.remove(reg);
                        // Mark this register as allocated for the caller.
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
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) {
                tempUsed[i] = false;
                // If this register was cached for a variable, invalidate
                // because the register no longer holds the variable's value.
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
