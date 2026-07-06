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
    private final StringBuilder sb;
    private int labelCounter;
    private final Deque<LoopLabels> loopStack;

    // Registers for expression evaluation
    private static final String[] TEMP_REGS = {"t0", "t1", "t2", "t3", "t4", "t5", "t6"};
    private static final int NUM_TEMPS = 7;
    private final boolean[] tempUsed = new boolean[NUM_TEMPS];

    // Current function context
    private FuncDef currentFunc;
    private final Map<String, Integer> localOffset = new HashMap<>(); // variable → offset from fp
    private int nextLocalOffset; // grows downward (negative)

    // Frame info
    private int frameSize;

    // Loop labels
    private record LoopLabels(String start, String end) {}

    public CodeGenerator(SemanticAnalyzer analyzer) {
        this.analyzer = analyzer;
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
        localOffset.clear();
        freeSpillSlots.clear();
        nextLocalOffset = -8; // skip past saved ra (-4) and saved fp (-8)

        // Allocate stack slots for parameters and locals
        // Parameters are passed in a0-a7, but we store them on stack for consistency

        // Count locals by walking the body
        countLocals(fd.body());

        // Reserve spill slots for expression evaluation.
        // Max spill depth = max nesting depth of binary expressions.
        // We scan the body to find the maximum spill depth needed.
        int maxSpillDepth = calcMaxSpillDepth(fd.body());
        nextSpillOffset = nextLocalOffset; // spill slots grow downward from local area
        // Pre-allocate spill slots (each is 4 bytes)
        int spillAreaSize = maxSpillDepth * 4;

        // Calculate frame size
        // Layout (high to low, fp = s0 = old sp):
        //   fp - 4:  saved ra
        //   fp - 8:  saved old fp
        //   fp - 12: local 0 / param 0
        //   ...
        //   (then spill area below locals)

        int savedRegsSize = 8; // ra + fp = 2 words = 8 bytes
        int localSize = -nextLocalOffset - savedRegsSize; // actual local bytes
        if (localSize < 0) localSize = 0;
        frameSize = savedRegsSize + localSize + spillAreaSize;
        // Align to 16 bytes
        frameSize = (frameSize + 15) & ~15;

        // Adjust nextSpillOffset to be relative to s0, starting after locals
        // Spill slots start at nextLocalOffset and go downward
        nextSpillOffset = nextLocalOffset;

        // Emit function label
        emit("");
        emitLabel(fd.name());

        // Prologue
        emit("addi", "sp", "sp", String.valueOf(-frameSize));
        emit("sw", "ra", (frameSize - 4) + "(sp)");   // save ra
        emit("sw", "s0", (frameSize - 8) + "(sp)");   // save fp
        emit("addi", "s0", "sp", String.valueOf(frameSize)); // fp = old sp

        // Store parameters into local slots
        Symbol funcSym = analyzer.getFuncSymbols().get(fd);
        if (funcSym != null && funcSym.getFuncParamNames() != null) {
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

        // Epilogue (common exit point for all returns)
        emitLabel(funcEpilogueLabel());
        emit("lw", "ra", (frameSize - 4) + "(sp)");
        emit("lw", "s0", (frameSize - 8) + "(sp)");
        emit("addi", "sp", "sp", String.valueOf(frameSize));
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
                for (Stmt s : b.stmts()) countLocals(s);
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
                // Regular binary: 1 spill slot for this level + max of children
                int leftDepth = calcMaxExprDepth(be.left());
                int rightDepth = calcMaxExprDepth(be.right());
                // Left is evaluated, spilled, then right is evaluated.
                // Max = 1 (this spill) + max(left depth while evaluating left,
                //   right depth while evaluating right)
                // But more precisely: during left eval, we don't have this spill yet.
                // During right eval, we have 1 spill (from this level).
                // So max depth = max(leftDepth, 1 + rightDepth)
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
        if (localOffset.containsKey(name)) {
            return localOffset.get(name);
        }
        nextLocalOffset -= 4;
        localOffset.put(name, nextLocalOffset);
        return nextLocalOffset;
    }

    private int getLocalOffset(String name) {
        Integer off = localOffset.get(name);
        if (off != null) return off;
        // For parameters not yet allocated
        nextLocalOffset -= 4;
        localOffset.put(name, nextLocalOffset);
        return nextLocalOffset;
    }

    // ========== Statement generation ==========

    private void genStmt(Stmt stmt) {
        switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) genStmt(s);
            }
            case NullStmt ignored -> {}
            case ExprStmt es -> {
                String r = genExpr(es.expr());
                freeReg(r);
            }
            case AssignStmt as_ -> {
                String r = genExpr(as_.value());
                Symbol sym = analyzer.getGlobalScope().lookup(as_.name());
                if (sym != null && sym.isGlobal() && !sym.isConst()) {
                    // Store to global variable
                    String addrReg = allocReg();
                    emit("la", addrReg, sym.getName());
                    emit("sw", r, "0(" + addrReg + ")");
                    freeReg(addrReg);
                } else {
                    int offset = getLocalOffset(as_.name());
                    emit("sw", r, offset + "(s0)");
                }
                freeReg(r);
            }
            case VarDecl vd -> {
                String r = genExpr(vd.initExpr());
                int offset = allocateLocal(vd.name());
                emit("sw", r, offset + "(s0)");
                freeReg(r);
            }
            case ConstDecl cd -> {
                String r = genExpr(cd.initExpr());
                int offset = allocateLocal(cd.name());
                emit("sw", r, offset + "(s0)");
                freeReg(r);
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

        String r = allocReg();
        if (sym.isGlobal()) {
            // Load from global address: la r, sym; lw r, 0(r)
            emit("la", r, sym.getName());
            emit("lw", r, "0(" + r + ")");
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

        // Evaluate left and keep in register.
        // Evaluate right into a different register.
        // Compute result = left OP right.
        // Note: if right evaluation involves function calls, t0-t6 are caller-saved
        // and leftReg will be clobbered. We handle this by spilling left to a
        // frame-relative slot (s0-relative) before evaluating right, which
        // keeps sp 16-byte aligned and avoids stack corruption.
        String leftReg = genExpr(be.left());
        int spillOffset = allocateSpillSlot();
        spillReg(leftReg, spillOffset);
        freeReg(leftReg);

        String rightReg = genExpr(be.right());
        String savedLeft = loadSpill(spillOffset);
        freeSpillSlot(spillOffset); // recycle for reuse

        String resultReg = allocReg();
        emit("mv", resultReg, savedLeft);
        freeReg(savedLeft);

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

        // Phase 2: Move accumulated args to a0-a7, loading spilled ones.
        // Compress out null entries (spilled args) and track spill offsets.
        int spillCursor = 0;
        for (int i = 0; i < argRegs.size(); i++) {
            String reg = argRegs.get(i);
            if (reg == null) {
                // This arg was spilled; find its offset and load it
                while (spillCursor < argSpillOffsets.size() &&
                       argSpillOffsets.get(spillCursor) == -1) {
                    spillCursor++;
                }
                int off = argSpillOffsets.get(spillCursor);
                reg = loadSpill(off);
                freeSpillSlot(off); // recycle for reuse
                argRegs.set(i, reg);
                spillCursor++;
            }
        }

        for (int i = 0; i < argRegs.size(); i++) {
            String reg = argRegs.get(i);
            if (reg != null) {
                emit("mv", "a" + i, reg);
                freeReg(reg);
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

    // ========== Register allocation ==========

    private String allocReg() {
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (!tempUsed[i]) {
                tempUsed[i] = true;
                return TEMP_REGS[i];
            }
        }
        throw new RuntimeException("out of temporary registers");
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
