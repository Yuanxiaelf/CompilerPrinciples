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
        nextLocalOffset = -8; // skip past saved ra (-4) and saved fp (-8)

        // Allocate stack slots for parameters and locals
        // Parameters are passed in a0-a7, but we store them on stack for consistency

        // Count locals by walking the body
        countLocals(fd.body());

        // Calculate frame size
        // Layout (high to low, fp = s0 = old sp):
        //   fp - 4:  saved ra
        //   fp - 8:  saved old fp
        //   fp - 12: local 0
        //   fp - 16: local 1
        //   ...

        int savedRegsSize = 8; // ra + fp = 2 words = 8 bytes
        int localSize = -nextLocalOffset - savedRegsSize; // actual local bytes
        if (localSize < 0) localSize = 0;
        frameSize = savedRegsSize + localSize;
        // Align to 16 bytes
        frameSize = (frameSize + 15) & ~15;

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
        // Also check nested blocks inside
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

        // Regular binary: eval left, save, eval right, combine
        String leftReg = genExpr(be.left());
        pushReg(leftReg);
        freeReg(leftReg); // free after saving to stack
        String rightReg = genExpr(be.right());
        String savedLeft = popReg();

        // Now savedLeft has left value, rightReg has right value
        // Copy savedLeft to a temp for the operation
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

        // Evaluate arguments into a0-a7 (and stack for overflow)
        // Save current temp regs to stack before call
        // Actually, caller-saved regs will be clobbered, so we need to
        // save any live temps.

        // Evaluate args and store in parameter registers
        List<String> argRegs = new ArrayList<>();
        for (int i = 0; i < numArgs && i < 8; i++) {
            String r = genExpr(ce.args().get(i));
            argRegs.add(r);
        }

        // Move evaluated args to a0-a7
        for (int i = 0; i < argRegs.size(); i++) {
            emit("mv", "a" + i, argRegs.get(i));
            freeReg(argRegs.get(i));
        }

        // Handle args beyond 8 (push to stack)
        for (int i = 8; i < numArgs; i++) {
            String r = genExpr(ce.args().get(i));
            // Push to stack (caller's responsibility)
            // For simplicity, use sp-relative stores
            int stackSlot = (i - 8) * 4;
            emit("sw", r, stackSlot + "(sp)");
            freeReg(r);
        }

        // Call function
        emit("call", ce.funcName());

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

    private void freeReg(String reg) {
        for (int i = 0; i < NUM_TEMPS; i++) {
            if (TEMP_REGS[i].equals(reg)) {
                tempUsed[i] = false;
                return;
            }
        }
    }

    // Stack-based save/restore for nested expressions
    private int pushDepth = 0;

    private void pushReg(String reg) {
        emit("addi", "sp", "sp", "-4");
        emit("sw", reg, "0(sp)");
        pushDepth++;
    }

    private String popReg() {
        String reg = allocReg();
        emit("lw", reg, "0(sp)");
        emit("addi", "sp", "sp", "4");
        pushDepth--;
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
