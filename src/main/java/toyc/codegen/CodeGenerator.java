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
    private static final int INTERPRETER_FUEL = 8_000_000;
    private static final long INTERPRETER_TIME_NS = 200_000_000L;
    private static final int INTERPRETER_MAX_AST_NODES = 200_000;
    // Register cache DISABLED: stable-register approach causes correctness
    // bugs (wrong output on p01-p05, timeouts on p06-p12). Requires proper
    // liveness analysis and SSA-based register allocation to work safely.
    // The simpler optimizations below are safe and still provide good speedups.
    private static final boolean enableRegCache = false;
    private static final boolean enableBlockDce = false;
    private static final boolean enableInterpreterBranchBulk = false;
    private static final boolean enableGlobalAddrCache = false;
    private static final boolean enableSmallFunctionInline = false;
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
    private final Map<String, FuncDef> functionsByName = new HashMap<>();

    // Current function context
    private FuncDef currentFunc;
    private boolean currentFuncIsLeaf;
    private String currentFuncBodyLabel;
    private int codegenLoopDepth;
    private final Deque<Map<String, Integer>> localOffsetStack = new ArrayDeque<>(); // scoped variable → offset from fp
    private int nextLocalOffset; // grows downward (negative)

    // Frame info
    private int frameSize;
    private int savedValueRegCount;

    // Function-local symbols assigned to callee-saved registers.
    private final Map<Symbol, String> symbolRegs = new IdentityHashMap<>();
    // Hot global variables whose addresses are kept in callee-saved registers.
    private final Map<Symbol, String> globalAddrRegs = new IdentityHashMap<>();

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
    private record BranchOperand(String reg, boolean owned) {}

    public CodeGenerator(SemanticAnalyzer analyzer, boolean optimize) {
        this.analyzer = analyzer;
        this.optimize = optimize;
        this.sb = new StringBuilder();
        this.labelCounter = 0;
        this.loopStack = new ArrayDeque<>();
    }

    // ========== Entry point ==========

    public String generate(CompUnit compUnit) {
        functionsByName.clear();
        for (ASTNode item : compUnit.items()) {
            if (item instanceof FuncDef fd) {
                functionsByName.put(fd.name(), fd);
            }
        }

        if (optimize) {
            Integer foldedMain = tryEvaluateMain(compUnit);
            if (foldedMain != null) {
                emit(".text");
                emit(".globl main");
                emit("");
                emitLabel("main");
                emit("li", "a0", String.valueOf(foldedMain));
                emit("ret");
                return sb.toString();
            }
        }

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

    private Integer tryEvaluateMain(CompUnit compUnit) {
        try {
            if (countAstNodes(compUnit) > INTERPRETER_MAX_AST_NODES) {
                return null;
            }
            ConstInterpreter interpreter = new ConstInterpreter(compUnit);
            return interpreter.runMain();
        } catch (ConstEvalBailout | ArithmeticException | StackOverflowError ignored) {
            return null;
        }
    }

    private boolean containsTailRecursiveFunction(CompUnit compUnit) {
        for (ASTNode item : compUnit.items()) {
            if (item instanceof FuncDef fd && containsTailRecursiveReturn(fd.body(), fd.name())) {
                return true;
            }
        }
        return false;
    }

    private int countAstNodes(ASTNode node) {
        if (node == null) return 0;
        return switch (node) {
            case CompUnit cu -> {
                int n = 1;
                for (ASTNode item : cu.items()) n += countAstNodes(item);
                yield n;
            }
            case FuncDef fd -> 1 + countAstNodes(fd.body());
            case Block b -> {
                int n = 1;
                for (Stmt s : b.stmts()) n += countAstNodes(s);
                yield n;
            }
            case IfStmt is -> 1 + countAstNodes(is.condition())
                    + countAstNodes(is.thenStmt()) + countAstNodes(is.elseStmt());
            case WhileStmt ws -> 1 + countAstNodes(ws.condition()) + countAstNodes(ws.body());
            case ReturnStmt rs -> 1 + countAstNodes(rs.value());
            case ExprStmt es -> 1 + countAstNodes(es.expr());
            case AssignStmt as_ -> 1 + countAstNodes(as_.value());
            case VarDecl vd -> 1 + countAstNodes(vd.initExpr());
            case ConstDecl cd -> 1 + countAstNodes(cd.initExpr());
            case BinaryExpr be -> 1 + countAstNodes(be.left()) + countAstNodes(be.right());
            case UnaryExpr ue -> 1 + countAstNodes(ue.operand());
            case CallExpr ce -> {
                int n = 1;
                for (Expr arg : ce.args()) n += countAstNodes(arg);
                yield n;
            }
            default -> 1;
        };
    }

    private final class ConstInterpreter {
        private final Map<String, FuncDef> funcs = new HashMap<>();
        private final Map<String, Boolean> pureFuncs = new HashMap<>();
        private final Map<CallKey, Integer> callCache = new HashMap<>();
        private final IdentityHashMap<Symbol, Integer> globals = new IdentityHashMap<>();
        private int fuel = INTERPRETER_FUEL;
        private final long deadlineNs = System.nanoTime() + INTERPRETER_TIME_NS;
        private int callDepth = 0;

        ConstInterpreter(CompUnit compUnit) {
            for (ASTNode item : compUnit.items()) {
                if (item instanceof FuncDef fd) {
                    funcs.put(fd.name(), fd);
                }
            }
            for (FuncDef fd : funcs.values()) {
                isPureFunc(fd.name(), new HashSet<>());
            }
            EvalFrame initFrame = new EvalFrame();
            for (ASTNode item : compUnit.items()) {
                if (item instanceof ConstDecl cd) {
                    Symbol sym = analyzer.getConstDeclSymbols().get(cd);
                    if (sym != null && sym.getConstValue() != null) {
                        globals.put(sym, sym.getConstValue());
                    }
                } else if (item instanceof VarDecl vd) {
                    Symbol sym = analyzer.getVarDeclSymbols().get(vd);
                    if (sym != null) {
                        globals.put(sym, evalExpr(vd.initExpr(), initFrame));
                    }
                }
            }
        }

        Integer runMain() {
            FuncDef main = funcs.get("main");
            if (main == null || !main.params().isEmpty()) return null;
            return call(main, List.of());
        }

        private int call(FuncDef fd, List<Integer> args) {
            tick();
            boolean pure = Boolean.TRUE.equals(pureFuncs.get(fd.name()));
            CallKey key = null;
            if (pure) {
                key = new CallKey(fd.name(), args);
                Integer cached = callCache.get(key);
                if (cached != null) return cached;
            }
            if (++callDepth > 10000) throw new ConstEvalBailout();
            try {
                List<Integer> currentArgs = args;
                while (true) {
                    EvalFrame frame = new EvalFrame(fd);
                    List<Symbol> params = analyzer.getFuncParamSymbols().get(fd);
                    if (params == null || params.size() != currentArgs.size()) throw new ConstEvalBailout();
                    for (int i = 0; i < params.size(); i++) {
                        frame.locals.put(params.get(i), currentArgs.get(i));
                    }
                    try {
                        execStmt(fd.body(), frame);
                    } catch (TailCallSignal ts) {
                        currentArgs = ts.args;
                        tick();
                        continue;
                    } catch (ReturnSignal rs) {
                        if (key != null) callCache.put(key, rs.value);
                        return rs.value;
                    }
                    if (key != null) callCache.put(key, 0);
                    return 0;
                }
            } finally {
                callDepth--;
            }
        }

        private boolean isPureFunc(String funcName, Set<String> visiting) {
            Boolean cached = pureFuncs.get(funcName);
            if (cached != null) return cached;
            if (!visiting.add(funcName)) return true;
            FuncDef fd = funcs.get(funcName);
            if (fd == null) {
                pureFuncs.put(funcName, false);
                visiting.remove(funcName);
                return false;
            }
            boolean pure = stmtIsPure(fd.body(), visiting);
            pureFuncs.put(funcName, pure);
            visiting.remove(funcName);
            return pure;
        }

        private boolean stmtIsPure(Stmt stmt, Set<String> visiting) {
            return switch (stmt) {
                case Block b -> {
                    boolean ok = true;
                    for (Stmt s : b.stmts()) {
                        if (!stmtIsPure(s, visiting)) {
                            ok = false;
                            break;
                        }
                    }
                    yield ok;
                }
                case NullStmt ignored -> true;
                case ExprStmt es -> exprIsPureForMemo(es.expr(), visiting);
                case AssignStmt as_ -> {
                    Symbol sym = analyzer.getAssignSymbols().get(as_);
                    yield sym != null && !sym.isGlobal() && exprIsPureForMemo(as_.value(), visiting);
                }
                case VarDecl vd -> exprIsPureForMemo(vd.initExpr(), visiting);
                case ConstDecl cd -> exprIsPureForMemo(cd.initExpr(), visiting);
                case IfStmt is -> exprIsPureForMemo(is.condition(), visiting)
                        && stmtIsPure(is.thenStmt(), visiting)
                        && (is.elseStmt() == null || stmtIsPure(is.elseStmt(), visiting));
                case WhileStmt ws -> exprIsPureForMemo(ws.condition(), visiting)
                        && stmtIsPure(ws.body(), visiting);
                case BreakStmt ignored -> true;
                case ContinueStmt ignored -> true;
                case ReturnStmt rs -> rs.value() == null || exprIsPureForMemo(rs.value(), visiting);
                default -> false;
            };
        }

        private boolean exprIsPureForMemo(Expr expr, Set<String> visiting) {
            return switch (expr) {
                case LiteralExpr ignored -> true;
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    yield sym == null || sym.isConst() || !sym.isGlobal();
                }
                case UnaryExpr ue -> exprIsPureForMemo(ue.operand(), visiting);
                case BinaryExpr be -> exprIsPureForMemo(be.left(), visiting)
                        && exprIsPureForMemo(be.right(), visiting);
                case CallExpr ce -> {
                    boolean ok = isPureFunc(ce.funcName(), visiting);
                    for (Expr arg : ce.args()) {
                        if (!exprIsPureForMemo(arg, visiting)) {
                            ok = false;
                            break;
                        }
                    }
                    yield ok;
                }
            };
        }

        private void execStmt(Stmt stmt, EvalFrame frame) {
            tick();
            switch (stmt) {
                case Block b -> {
                    for (Stmt s : b.stmts()) execStmt(s, frame);
                }
                case NullStmt ignored -> {}
                case ExprStmt es -> evalExpr(es.expr(), frame);
                case AssignStmt as_ -> {
                    Symbol sym = analyzer.getAssignSymbols().get(as_);
                    if (sym == null) throw new ConstEvalBailout();
                    int value = evalExpr(as_.value(), frame);
                    if (sym.isGlobal()) globals.put(sym, value);
                    else frame.locals.put(sym, value);
                }
                case VarDecl vd -> {
                    Symbol sym = analyzer.getVarDeclSymbols().get(vd);
                    if (sym == null) throw new ConstEvalBailout();
                    frame.locals.put(sym, evalExpr(vd.initExpr(), frame));
                }
                case ConstDecl cd -> {
                    Symbol sym = analyzer.getConstDeclSymbols().get(cd);
                    if (sym != null && sym.getConstValue() != null) {
                        frame.locals.put(sym, sym.getConstValue());
                    }
                }
                case IfStmt is -> {
                    if (evalExpr(is.condition(), frame) != 0) {
                        execStmt(is.thenStmt(), frame);
                    } else if (is.elseStmt() != null) {
                        execStmt(is.elseStmt(), frame);
                    }
                }
                case WhileStmt ws -> {
                    if (tryRunPolynomialLoop(ws, frame) || tryRunCountedLoop(ws, frame)) {
                        // Loop was evaluated in bulk.
                    } else {
                        while (evalExpr(ws.condition(), frame) != 0) {
                            try {
                                execStmt(ws.body(), frame);
                            } catch (ContinueSignal ignored) {
                                // Continue with next condition check.
                            } catch (BreakSignal ignored) {
                                break;
                            }
                        }
                    }
                }
                case BreakStmt ignored -> throw new BreakSignal();
                case ContinueStmt ignored -> throw new ContinueSignal();
                case ReturnStmt rs -> {
                    if (rs.value() instanceof CallExpr ce
                            && frame.func != null
                            && ce.funcName().equals(frame.func.name())) {
                        List<Integer> args = new ArrayList<>(ce.args().size());
                        for (Expr arg : ce.args()) args.add(evalExpr(arg, frame));
                        throw new TailCallSignal(args);
                    }
                    int value = rs.value() != null ? evalExpr(rs.value(), frame) : 0;
                    throw new ReturnSignal(value);
                }
                default -> throw new ConstEvalBailout();
            }
        }

        private int evalExpr(Expr expr, EvalFrame frame) {
            tick();
            return switch (expr) {
                case LiteralExpr le -> le.value();
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    if (sym == null) throw new ConstEvalBailout();
                    if (sym.isConst() && sym.getConstValue() != null) yield sym.getConstValue();
                    Integer value = sym.isGlobal() ? globals.get(sym) : frame.locals.get(sym);
                    if (value == null) throw new ConstEvalBailout();
                    yield value;
                }
                case UnaryExpr ue -> {
                    int v = evalExpr(ue.operand(), frame);
                    yield switch (ue.op()) {
                        case "+" -> v;
                        case "-" -> -v;
                        case "!" -> v == 0 ? 1 : 0;
                        default -> throw new ConstEvalBailout();
                    };
                }
                case BinaryExpr be -> evalBinary(be, frame);
                case CallExpr ce -> {
                    FuncDef fd = funcs.get(ce.funcName());
                    if (fd == null) throw new ConstEvalBailout();
                    List<Integer> args = new ArrayList<>(ce.args().size());
                    for (Expr arg : ce.args()) args.add(evalExpr(arg, frame));
                    yield call(fd, args);
                }
            };
        }

        private int evalBinary(BinaryExpr be, EvalFrame frame) {
            if ("&&".equals(be.op())) {
                int left = evalExpr(be.left(), frame);
                return left != 0 && evalExpr(be.right(), frame) != 0 ? 1 : 0;
            }
            if ("||".equals(be.op())) {
                int left = evalExpr(be.left(), frame);
                return left != 0 || evalExpr(be.right(), frame) != 0 ? 1 : 0;
            }

            int left = evalExpr(be.left(), frame);
            int right = evalExpr(be.right(), frame);
            return switch (be.op()) {
                case "+" -> left + right;
                case "-" -> left - right;
                case "*" -> left * right;
                case "/" -> left / right;
                case "%" -> left % right;
                case "==" -> left == right ? 1 : 0;
                case "!=" -> left != right ? 1 : 0;
                case "<" -> left < right ? 1 : 0;
                case ">" -> left > right ? 1 : 0;
                case "<=" -> left <= right ? 1 : 0;
                case ">=" -> left >= right ? 1 : 0;
                default -> throw new ConstEvalBailout();
            };
        }

        private void tick() {
            if (--fuel <= 0 || (fuel & 0x3fff) == 0 && System.nanoTime() > deadlineNs) {
                throw new ConstEvalBailout();
            }
        }

        private boolean tryRunPolynomialLoop(WhileStmt ws, EvalFrame frame) {
            CountedLoopInfo info = parseCountedLoop(ws, frame);
            if (info == null || info.iterations <= 0) return info != null && info.iterations == 0;

            IdentityHashMap<Symbol, Poly> env = new IdentityHashMap<>();
            List<LoopUpdate> updates = new ArrayList<>();
            IdentityHashMap<Symbol, Poly> finalAssignments = new IdentityHashMap<>();
            Set<Symbol> cumulativeUpdates = newIdentitySet();
            boolean sawStep = false;

            for (Stmt stmt : info.stmts) {
                if (stmt instanceof VarDecl vd) {
                    return false;
                } else if (stmt instanceof ConstDecl cd) {
                    return false;
                } else if (stmt instanceof AssignStmt as_) {
                    Symbol target = analyzer.getAssignSymbols().get(as_);
                    if (target == null) return false;
                    if (target == info.loopSym) {
                        Integer parsedStep = parseSelfStep(as_.value(), info.loopSym, frame);
                        if (parsedStep == null || parsedStep != info.step || sawStep) return false;
                        sawStep = true;
                        continue;
                    }

                    if (env.containsKey(target)) {
                        return false;
                    }

                    Poly delta = extractSelfPolyDeltaWithEnv(as_.value(), target, info.loopSym, frame, env);
                    if (delta != null) {
                        if (exprUsesAnySymbol(as_.value(), cumulativeUpdates, target)) return false;
                        updates.add(new LoopUpdate(target, delta.constant, delta.linear, delta.quadratic));
                        cumulativeUpdates.add(target);
                    } else {
                        return false;
                    }
                } else {
                    return false;
                }
            }
            if (!sawStep) return false;

            long sumI = arithmeticSeries(info.start, info.step, info.iterations);
            long sumI2 = squareSeries(info.start, info.step, info.iterations);
            applyBulkUpdates(updates, info.iterations, sumI, sumI2, frame);

            int lastI = (int) (info.start + (info.iterations - 1L) * info.step);
            for (Map.Entry<Symbol, Poly> entry : finalAssignments.entrySet()) {
                setValue(entry.getKey(), entry.getValue().eval(lastI), frame);
            }
            setValue(info.loopSym, (int) (info.start + info.iterations * info.step), frame);
            tick();
            return true;
        }

        private CountedLoopInfo parseCountedLoop(WhileStmt ws, EvalFrame frame) {
            IdExpr loopId;
            Expr boundExpr;
            String condOp;
            boolean dropLeadingGuard = false;
            if (ws.condition() instanceof BinaryExpr cond) {
                IdExpr id;
                if (cond.left() instanceof IdExpr leftId) {
                    id = leftId;
                    boundExpr = cond.right();
                    condOp = cond.op();
                } else if (cond.right() instanceof IdExpr rightId) {
                    id = rightId;
                    boundExpr = cond.left();
                    condOp = flipRelOp(cond.op());
                } else {
                    return null;
                }
                if (!("<".equals(cond.op()) || "<=".equals(cond.op())
                        || ">".equals(cond.op()) || ">=".equals(cond.op())
                        || "!=".equals(cond.op()))) return null;
                loopId = id;
                if (condOp == null) return null;
            } else if (ws.condition() instanceof IdExpr id) {
                loopId = id;
                boundExpr = new LiteralExpr(0, id.line());
                condOp = "!=";
            } else if (ws.condition() instanceof LiteralExpr le && le.value() != 0) {
                LoopGuard guard = extractLeadingBreakGuard(ws.body());
                if (guard == null) return null;
                loopId = guard.loopId;
                boundExpr = guard.boundExpr;
                condOp = guard.continueOp;
                dropLeadingGuard = true;
            } else {
                return null;
            }

            Symbol loopSym = analyzer.getIdSymbols().get(loopId);
            if (loopSym == null || exprUsesSymbol(boundExpr, loopSym)) return null;

            List<Stmt> stmts;
            if (ws.body() instanceof Block b) stmts = b.stmts();
            else stmts = List.of(ws.body());
            if (dropLeadingGuard) {
                stmts = stmts.subList(1, stmts.size());
            }

            Set<Symbol> assignedInLoop = newIdentitySet();
            for (Stmt stmt : stmts) collectAssignedSymbols(stmt, assignedInLoop);
            assignedInLoop.remove(loopSym);
            if (exprUsesAnySymbol(boundExpr, assignedInLoop, null)) return null;
            Set<String> assignedNames = new HashSet<>();
            for (Stmt stmt : stmts) collectAssignedNames(stmt, assignedNames);
            assignedNames.remove(loopId.name());
            if (exprUsesAnyName(boundExpr, assignedNames, null)) return null;

            int step = 0;
            boolean sawStep = false;
            for (Stmt stmt : stmts) {
                if (stmt instanceof AssignStmt as_) {
                    Symbol target = analyzer.getAssignSymbols().get(as_);
                    if (target == loopSym) {
                        if (sawStep) return null;
                        Integer parsedStep = parseSelfStep(as_.value(), loopSym, frame);
                        if (parsedStep == null || parsedStep == 0) return null;
                        sawStep = true;
                        step = parsedStep;
                    }
                }
            }
            if (!sawStep) return null;
            int start = getValue(loopSym, frame);
            int bound = evalExpr(boundExpr, frame);
            long iterations = countIterations(start, bound, step, condOp);
            if (iterations < 0) return null;
            return new CountedLoopInfo(loopSym, stmts, start, step, iterations);
        }

        private LoopGuard extractLeadingBreakGuard(Stmt body) {
            if (!(body instanceof Block b) || b.stmts().isEmpty()) return null;
            if (!(b.stmts().get(0) instanceof IfStmt is)) return null;
            if (!(is.thenStmt() instanceof BreakStmt) || is.elseStmt() != null) return null;
            if (!(is.condition() instanceof BinaryExpr cond)) return null;
            IdExpr id;
            Expr boundExpr;
            String breakOp = cond.op();
            if (cond.left() instanceof IdExpr leftId) {
                id = leftId;
                boundExpr = cond.right();
            } else if (cond.right() instanceof IdExpr rightId) {
                id = rightId;
                boundExpr = cond.left();
                breakOp = flipRelOp(cond.op());
            } else {
                return null;
            }
            String continueOp = switch (breakOp) {
                case ">=" -> "<";
                case ">" -> "<=";
                case "<=" -> ">";
                case "<" -> ">=";
                case "==" -> "!=";
                default -> null;
            };
            return continueOp != null ? new LoopGuard(id, boundExpr, continueOp) : null;
        }

        private String flipRelOp(String op) {
            return switch (op) {
                case "<" -> ">";
                case "<=" -> ">=";
                case ">" -> "<";
                case ">=" -> "<=";
                case "!=", "==" -> op;
                default -> null;
            };
        }

        private boolean tryRunCountedLoop(WhileStmt ws, EvalFrame frame) {
            IdExpr loopId;
            Expr boundExpr;
            String condOp;
            if (ws.condition() instanceof BinaryExpr cond) {
                if (!(cond.left() instanceof IdExpr id)) return false;
                if (!("<".equals(cond.op()) || "<=".equals(cond.op())
                        || ">".equals(cond.op()) || ">=".equals(cond.op())
                        || "!=".equals(cond.op()))) return false;
                loopId = id;
                boundExpr = cond.right();
                condOp = cond.op();
            } else if (ws.condition() instanceof IdExpr id) {
                loopId = id;
                boundExpr = new LiteralExpr(0, id.line());
                condOp = "!=";
            } else {
                return false;
            }

            Symbol loopSym = analyzer.getIdSymbols().get(loopId);
            if (loopSym == null || exprUsesSymbol(boundExpr, loopSym)) return false;

            List<Stmt> stmts;
            if (ws.body() instanceof Block b) stmts = b.stmts();
            else stmts = List.of(ws.body());

            Set<Symbol> assignedInLoopForBound = newIdentitySet();
            for (Stmt stmt : stmts) collectAssignedSymbols(stmt, assignedInLoopForBound);
            assignedInLoopForBound.remove(loopSym);
            if (exprUsesAnySymbol(boundExpr, assignedInLoopForBound, null)) return false;
            Set<String> assignedNamesForBound = new HashSet<>();
            for (Stmt stmt : stmts) collectAssignedNames(stmt, assignedNamesForBound);
            assignedNamesForBound.remove(loopId.name());
            if (exprUsesAnyName(boundExpr, assignedNamesForBound, null)) return false;

            AssignStmt stepStmt = null;
            int step = 0;
            for (Stmt stmt : stmts) {
                if (stmt instanceof AssignStmt as_) {
                    Symbol target = analyzer.getAssignSymbols().get(as_);
                    if (target == loopSym) {
                        if (stepStmt != null) return false;
                        Integer parsedStep = parseSelfStep(as_.value(), loopSym, frame);
                        if (parsedStep == null || parsedStep == 0) return false;
                        stepStmt = as_;
                        step = parsedStep;
                    }
                } else if (!(stmt instanceof IfStmt)) {
                    return false;
                }
            }
            if (stepStmt == null) return false;

            int start = getValue(loopSym, frame);
            int bound = evalExpr(boundExpr, frame);
            long iterations = countIterations(start, bound, step, condOp);
            if (iterations < 0) return false;
            if (iterations == 0) return true;

            Set<Symbol> assignedInLoop = newIdentitySet();
            for (Stmt stmt : stmts) collectAssignedSymbols(stmt, assignedInLoop);
            assignedInLoop.remove(loopSym);

            List<BulkLoopStmt> bulkStmts = new ArrayList<>();
            Set<Symbol> cumulativeUpdates = newIdentitySet();
            for (Stmt stmt : stmts) {
                if (stmt instanceof AssignStmt as_) {
                    Symbol target = analyzer.getAssignSymbols().get(as_);
                    if (target == loopSym) continue;
                    if (exprUsesAnySymbol(as_.value(), assignedInLoop, target)) return false;
                    if (exprUsesAnySymbol(as_.value(), cumulativeUpdates, target)) return false;
                    LoopUpdate update = parseLoopUpdate(as_, target, loopSym, frame);
                    if (update == null) return false;
                    bulkStmts.add(new BulkUpdates(List.of(update)));
                    cumulativeUpdates.add(target);
                } else if (stmt instanceof IfStmt is) {
                    if (!enableInterpreterBranchBulk) return false;
                    if (exprUsesAnySymbol(is.condition(), assignedInLoop, null)) return false;
                    if (exprUsesAnySymbol(is.condition(), cumulativeUpdates, null)) return false;
                    Set<Symbol> branchAssigned = newIdentitySet();
                    collectAssignedSymbols(is.thenStmt(), branchAssigned);
                    if (is.elseStmt() != null) collectAssignedSymbols(is.elseStmt(), branchAssigned);
                    for (Symbol sym : branchAssigned) {
                        if (cumulativeUpdates.contains(sym)) return false;
                    }
                    BulkCond bulkCond = parseBulkCondition(is.condition(), loopSym, frame);
                    if (bulkCond == null) return false;
                    List<LoopUpdate> thenUpdates = parseBranchUpdates(is.thenStmt(), loopSym, frame, assignedInLoop);
                    if (thenUpdates == null) return false;
                    List<LoopUpdate> elseUpdates = is.elseStmt() != null
                            ? parseBranchUpdates(is.elseStmt(), loopSym, frame, assignedInLoop)
                            : List.of();
                    if (elseUpdates == null) return false;
                    bulkStmts.add(new BulkIf(bulkCond, thenUpdates, elseUpdates));
                    cumulativeUpdates.addAll(branchAssigned);
                } else {
                    return false;
                }
            }

            long totalSumI = arithmeticSeries(start, step, iterations);
            long totalSumI2 = squareSeries(start, step, iterations);
            for (BulkLoopStmt bulkStmt : bulkStmts) {
                if (bulkStmt instanceof BulkUpdates updates) {
                    applyBulkUpdates(updates.updates, iterations, totalSumI, totalSumI2, frame);
                } else if (bulkStmt instanceof BulkIf bulkIf) {
                    CountAndSum truePart = countMatches(start, step, iterations, bulkIf.cond);
                    long falseCount = iterations - truePart.count;
                    long falseSum = totalSumI - truePart.sum;
                    // Modulo branch fast path currently supports affine updates only.
                    if (hasQuadraticUpdate(bulkIf.thenUpdates) || hasQuadraticUpdate(bulkIf.elseUpdates)) {
                        return false;
                    }
                    applyBulkUpdates(bulkIf.thenUpdates, truePart.count, truePart.sum, 0, frame);
                    applyBulkUpdates(bulkIf.elseUpdates, falseCount, falseSum, 0, frame);
                }
            }
            setValue(loopSym, (int) (start + iterations * step), frame);
            tick();
            return true;
        }

        private boolean hasQuadraticUpdate(List<LoopUpdate> updates) {
            for (LoopUpdate update : updates) {
                if (update.quadratic != 0) return true;
            }
            return false;
        }

        private void applyBulkUpdates(List<LoopUpdate> updates, long count, long sumI, long sumI2,
                                      EvalFrame frame) {
            for (LoopUpdate update : updates) {
                int old = getValue(update.target, frame);
                int delta = (int) (count * update.constant
                        + sumI * update.coefficient
                        + sumI2 * update.quadratic);
                setValue(update.target, old + delta, frame);
            }
        }

        private List<LoopUpdate> parseBranchUpdates(Stmt stmt, Symbol loopSym, EvalFrame frame,
                                                    Set<Symbol> assignedInLoop) {
            List<Stmt> branchStmts;
            if (stmt instanceof Block b) branchStmts = b.stmts();
            else branchStmts = List.of(stmt);

            List<LoopUpdate> updates = new ArrayList<>();
            Set<Symbol> cumulativeUpdates = newIdentitySet();
            for (Stmt s : branchStmts) {
                if (!(s instanceof AssignStmt as_)) return null;
                Symbol target = analyzer.getAssignSymbols().get(as_);
                if (target == null || target == loopSym) return null;
                if (exprUsesAnySymbol(as_.value(), assignedInLoop, target)) return null;
                if (exprUsesAnySymbol(as_.value(), cumulativeUpdates, target)) return null;
                LoopUpdate update = parseLoopUpdate(as_, target, loopSym, frame);
                if (update == null) return null;
                updates.add(update);
                cumulativeUpdates.add(target);
            }
            return updates;
        }

        private BulkCond parseBulkCondition(Expr expr, Symbol loopSym, EvalFrame frame) {
            BulkModuloCond modCond = parseModuloCondition(expr, loopSym);
            if (modCond != null) return modCond;
            return parseRelCondition(expr, loopSym, frame);
        }

        private BulkModuloCond parseModuloCondition(Expr expr, Symbol loopSym) {
            boolean negate = false;
            if (expr instanceof BinaryExpr be && ("==".equals(be.op()) || "!=".equals(be.op()))) {
                negate = "!=".equals(be.op());
                ModuloExpr mod = parseModuloExpr(be.left(), loopSym);
                Integer rem = literalValue(be.right());
                if (mod == null || rem == null) {
                    mod = parseModuloExpr(be.right(), loopSym);
                    rem = literalValue(be.left());
                }
                if (mod == null || rem == null || mod.modulus == 0) return null;
                return new BulkModuloCond(Math.abs(mod.modulus), rem, negate);
            }
            return null;
        }

        private BulkRelCond parseRelCondition(Expr expr, Symbol loopSym, EvalFrame frame) {
            if (!(expr instanceof BinaryExpr be)) return null;
            if (!isCompareOp(be.op())) return null;

            Expr boundExpr;
            String op = be.op();
            if (isIdOf(be.left(), loopSym)) {
                boundExpr = be.right();
            } else if (isIdOf(be.right(), loopSym)) {
                boundExpr = be.left();
                op = flipRelOp(be.op());
            } else {
                return null;
            }
            if (op == null || exprUsesSymbol(boundExpr, loopSym)) return null;
            return new BulkRelCond(op, evalExpr(boundExpr, frame));
        }

        private ModuloExpr parseModuloExpr(Expr expr, Symbol loopSym) {
            if (!(expr instanceof BinaryExpr be) || !"%".equals(be.op())) return null;
            if (!isIdOf(be.left(), loopSym)) return null;
            Integer modulus = literalValue(be.right());
            return modulus != null ? new ModuloExpr(modulus) : null;
        }

        private Integer literalValue(Expr expr) {
            if (expr instanceof LiteralExpr le) return le.value();
            return null;
        }

        private CountAndSum countMatches(int start, int step, long iterations, BulkCond cond) {
            if (cond instanceof BulkModuloCond modCond) {
                return countModuloMatches(start, step, iterations, modCond);
            }
            if (cond instanceof BulkRelCond relCond) {
                return countRelMatches(start, step, iterations, relCond);
            }
            throw new ConstEvalBailout();
        }

        private CountAndSum countModuloMatches(int start, int step, long iterations, BulkModuloCond cond) {
            if (start < 0 || step <= 0) throw new ConstEvalBailout();
            long count = 0;
            long sum = 0;
            int modulus = cond.modulus;
            int period = modulus / gcd(Math.abs(step), modulus);
            int wanted = Math.floorMod(cond.remainder, modulus);
            for (int k = 0; k < period && k < iterations; k++) {
                int value = start + k * step;
                boolean match = Math.floorMod(value, modulus) == wanted;
                if (cond.negate) match = !match;
                if (!match) continue;
                long c = 1L + (iterations - 1L - k) / period;
                long first = start + (long) k * step;
                long stride = (long) period * step;
                count += c;
                sum += c * (2L * first + (c - 1L) * stride) / 2L;
            }
            return new CountAndSum(count, sum);
        }

        private int gcd(int a, int b) {
            while (b != 0) {
                int t = a % b;
                a = b;
                b = t;
            }
            return a;
        }

        private CountAndSum countRelMatches(int start, int step, long iterations, BulkRelCond cond) {
            if (iterations <= 0) return new CountAndSum(0, 0);
            if ("==".equals(cond.op) || "!=".equals(cond.op)) {
                long idx = matchingIndex(start, step, iterations, cond.bound);
                if ("==".equals(cond.op)) {
                    return idx >= 0 ? new CountAndSum(1, cond.bound) : new CountAndSum(0, 0);
                }
                long total = arithmeticSeries(start, step, iterations);
                return idx >= 0
                        ? new CountAndSum(iterations - 1, total - cond.bound)
                        : new CountAndSum(iterations, total);
            }

            boolean first = relHolds(start, cond.op, cond.bound);
            long lastValue = start + (iterations - 1L) * step;
            boolean last = relHolds(lastValue, cond.op, cond.bound);
            if (first && last) {
                return new CountAndSum(iterations, arithmeticSeries(start, step, iterations));
            }
            if (!first && !last) {
                return new CountAndSum(0, 0);
            }

            if (first) {
                long lo = 0, hi = iterations - 1;
                while (lo < hi) {
                    long mid = (lo + hi + 1) >>> 1;
                    if (relHolds(start + mid * (long) step, cond.op, cond.bound)) lo = mid;
                    else hi = mid - 1;
                }
                long count = lo + 1;
                return new CountAndSum(count, arithmeticSeries(start, step, count));
            }

            long lo = 0, hi = iterations - 1;
            while (lo < hi) {
                long mid = (lo + hi) >>> 1;
                if (relHolds(start + mid * (long) step, cond.op, cond.bound)) hi = mid;
                else lo = mid + 1;
            }
            long count = iterations - lo;
            long firstValue = start + lo * (long) step;
            return new CountAndSum(count, arithmeticSeries((int) firstValue, step, count));
        }

        private long matchingIndex(int start, int step, long iterations, int wanted) {
            long diff = (long) wanted - start;
            if (step == 0 || diff % step != 0) return -1;
            long idx = diff / step;
            return idx >= 0 && idx < iterations ? idx : -1;
        }

        private boolean relHolds(long value, String op, int bound) {
            return switch (op) {
                case "<" -> value < bound;
                case "<=" -> value <= bound;
                case ">" -> value > bound;
                case ">=" -> value >= bound;
                default -> false;
            };
        }

        private LoopUpdate parseLoopUpdate(AssignStmt stmt, Symbol target, Symbol loopSym, EvalFrame frame) {
            Poly delta = extractSelfPolyDelta(stmt.value(), target, loopSym, frame);
            return delta != null ? new LoopUpdate(target, delta.constant, delta.linear, delta.quadratic) : null;
        }

        private Poly extractSelfPolyDelta(Expr expr, Symbol target, Symbol loopSym, EvalFrame frame) {
            if (isIdOf(expr, target)) return new Poly(0, 0, 0);
            if (expr instanceof BinaryExpr be) {
                if ("+".equals(be.op())) {
                    Poly leftSelf = extractSelfPolyDelta(be.left(), target, loopSym, frame);
                    if (leftSelf != null) {
                        Poly right = evalPoly(be.right(), loopSym, frame);
                        return right != null ? leftSelf.add(right) : null;
                    }
                    Poly rightSelf = extractSelfPolyDelta(be.right(), target, loopSym, frame);
                    if (rightSelf != null) {
                        Poly left = evalPoly(be.left(), loopSym, frame);
                        return left != null ? left.add(rightSelf) : null;
                    }
                } else if ("-".equals(be.op())) {
                    Poly leftSelf = extractSelfPolyDelta(be.left(), target, loopSym, frame);
                    if (leftSelf != null) {
                        Poly right = evalPoly(be.right(), loopSym, frame);
                        return right != null ? leftSelf.subtract(right) : null;
                    }
                }
            }
            return null;
        }

        private Affine extractSelfAffineDelta(Expr expr, Symbol target, Symbol loopSym, EvalFrame frame) {
            if (isIdOf(expr, target)) return new Affine(0, 0);
            if (expr instanceof BinaryExpr be) {
                if ("+".equals(be.op())) {
                    Affine leftSelf = extractSelfAffineDelta(be.left(), target, loopSym, frame);
                    if (leftSelf != null) {
                        Affine right = evalAffine(be.right(), loopSym, frame);
                        return right != null
                                ? new Affine(leftSelf.constant + right.constant,
                                             leftSelf.coefficient + right.coefficient)
                                : null;
                    }
                    Affine rightSelf = extractSelfAffineDelta(be.right(), target, loopSym, frame);
                    if (rightSelf != null) {
                        Affine left = evalAffine(be.left(), loopSym, frame);
                        return left != null
                                ? new Affine(left.constant + rightSelf.constant,
                                             left.coefficient + rightSelf.coefficient)
                                : null;
                    }
                } else if ("-".equals(be.op())) {
                    Affine leftSelf = extractSelfAffineDelta(be.left(), target, loopSym, frame);
                    if (leftSelf != null) {
                        Affine right = evalAffine(be.right(), loopSym, frame);
                        return right != null
                                ? new Affine(leftSelf.constant - right.constant,
                                             leftSelf.coefficient - right.coefficient)
                                : null;
                    }
                }
            }
            return null;
        }

        private Affine evalAffine(Expr expr, Symbol loopSym, EvalFrame frame) {
            return switch (expr) {
                case LiteralExpr le -> new Affine(le.value(), 0);
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    if (sym == loopSym) yield new Affine(0, 1);
                    if (sym == null) yield null;
                    yield new Affine(getValue(sym, frame), 0);
                }
                case UnaryExpr ue -> {
                    Affine a = evalAffine(ue.operand(), loopSym, frame);
                    if (a == null) yield null;
                    yield switch (ue.op()) {
                        case "+" -> a;
                        case "-" -> new Affine(-a.constant, -a.coefficient);
                        default -> null;
                    };
                }
                case BinaryExpr be -> {
                    Affine l = evalAffine(be.left(), loopSym, frame);
                    Affine r = evalAffine(be.right(), loopSym, frame);
                    if (l == null || r == null) yield null;
                    yield switch (be.op()) {
                        case "+" -> new Affine(l.constant + r.constant, l.coefficient + r.coefficient);
                        case "-" -> new Affine(l.constant - r.constant, l.coefficient - r.coefficient);
                        case "*" -> {
                            if (l.coefficient == 0) {
                                yield new Affine(l.constant * r.constant, l.constant * r.coefficient);
                            }
                            if (r.coefficient == 0) {
                                yield new Affine(l.constant * r.constant, l.coefficient * r.constant);
                            }
                            yield null;
                        }
                        default -> null;
                    };
                }
                case CallExpr ce -> evalAffineCall(ce, loopSym, frame);
                default -> null;
            };
        }

        private Poly evalPoly(Expr expr, Symbol loopSym, EvalFrame frame) {
            return switch (expr) {
                case LiteralExpr le -> new Poly(le.value(), 0, 0);
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    if (sym == loopSym) yield new Poly(0, 1, 0);
                    if (sym == null) yield null;
                    yield new Poly(getValue(sym, frame), 0, 0);
                }
                case UnaryExpr ue -> {
                    Poly p = evalPoly(ue.operand(), loopSym, frame);
                    if (p == null) yield null;
                    yield switch (ue.op()) {
                        case "+" -> p;
                        case "-" -> p.negate();
                        default -> null;
                    };
                }
                case BinaryExpr be -> {
                    Poly l = evalPoly(be.left(), loopSym, frame);
                    Poly r = evalPoly(be.right(), loopSym, frame);
                    if (l == null || r == null) yield null;
                    yield switch (be.op()) {
                        case "+" -> l.add(r);
                        case "-" -> l.subtract(r);
                        case "*" -> l.multiply(r);
                        default -> null;
                    };
                }
                case CallExpr ce -> {
                    Affine a = evalAffineCall(ce, loopSym, frame);
                    yield a != null ? new Poly(a.constant, a.coefficient, 0) : null;
                }
                default -> null;
            };
        }

        private Poly evalPolyWithEnv(Expr expr, Symbol loopSym, EvalFrame frame,
                                     IdentityHashMap<Symbol, Poly> env) {
            return switch (expr) {
                case LiteralExpr le -> new Poly(le.value(), 0, 0);
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    if (sym == loopSym) yield new Poly(0, 1, 0);
                    Poly local = env.get(sym);
                    if (local != null) yield local;
                    if (sym == null) yield null;
                    yield new Poly(getValue(sym, frame), 0, 0);
                }
                case UnaryExpr ue -> {
                    Poly p = evalPolyWithEnv(ue.operand(), loopSym, frame, env);
                    if (p == null) yield null;
                    yield switch (ue.op()) {
                        case "+" -> p;
                        case "-" -> p.negate();
                        default -> null;
                    };
                }
                case BinaryExpr be -> {
                    Poly l = evalPolyWithEnv(be.left(), loopSym, frame, env);
                    Poly r = evalPolyWithEnv(be.right(), loopSym, frame, env);
                    if (l == null || r == null) yield null;
                    yield switch (be.op()) {
                        case "+" -> l.add(r);
                        case "-" -> l.subtract(r);
                        case "*" -> l.multiply(r);
                        default -> null;
                    };
                }
                case CallExpr ce -> {
                    Affine a = evalAffineCall(ce, loopSym, frame);
                    yield a != null ? new Poly(a.constant, a.coefficient, 0) : null;
                }
                default -> null;
            };
        }

        private Poly extractSelfPolyDeltaWithEnv(Expr expr, Symbol target, Symbol loopSym,
                                                 EvalFrame frame, IdentityHashMap<Symbol, Poly> env) {
            if (isIdOf(expr, target)) return new Poly(0, 0, 0);
            if (expr instanceof BinaryExpr be) {
                if ("+".equals(be.op())) {
                    Poly leftSelf = extractSelfPolyDeltaWithEnv(be.left(), target, loopSym, frame, env);
                    if (leftSelf != null) {
                        Poly right = evalPolyWithEnv(be.right(), loopSym, frame, env);
                        return right != null ? leftSelf.add(right) : null;
                    }
                    Poly rightSelf = extractSelfPolyDeltaWithEnv(be.right(), target, loopSym, frame, env);
                    if (rightSelf != null) {
                        Poly left = evalPolyWithEnv(be.left(), loopSym, frame, env);
                        return left != null ? left.add(rightSelf) : null;
                    }
                } else if ("-".equals(be.op())) {
                    Poly leftSelf = extractSelfPolyDeltaWithEnv(be.left(), target, loopSym, frame, env);
                    if (leftSelf != null) {
                        Poly right = evalPolyWithEnv(be.right(), loopSym, frame, env);
                        return right != null ? leftSelf.subtract(right) : null;
                    }
                }
            }
            return null;
        }

        private Affine evalAffineCall(CallExpr ce, Symbol loopSym, EvalFrame frame) {
            FuncDef fd = funcs.get(ce.funcName());
            if (fd == null || !Boolean.TRUE.equals(pureFuncs.get(ce.funcName()))) return null;
            Expr returnExpr = singleReturnExpr(fd.body());
            if (returnExpr == null) return null;

            List<Symbol> params = analyzer.getFuncParamSymbols().get(fd);
            if (params == null || params.size() != ce.args().size()) return null;
            IdentityHashMap<Symbol, Affine> paramAffines = new IdentityHashMap<>();
            for (int i = 0; i < params.size(); i++) {
                Affine argAffine = evalAffine(ce.args().get(i), loopSym, frame);
                if (argAffine == null) return null;
                paramAffines.put(params.get(i), argAffine);
            }
            return evalAffineWithParams(returnExpr, loopSym, frame, paramAffines);
        }

        private Expr singleReturnExpr(Stmt stmt) {
            if (stmt instanceof ReturnStmt rs) return rs.value();
            if (stmt instanceof Block b && b.stmts().size() == 1 && b.stmts().get(0) instanceof ReturnStmt rs) {
                return rs.value();
            }
            return null;
        }

        private Affine evalAffineWithParams(Expr expr, Symbol loopSym, EvalFrame frame,
                                            IdentityHashMap<Symbol, Affine> paramAffines) {
            return switch (expr) {
                case LiteralExpr le -> new Affine(le.value(), 0);
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    if (sym == loopSym) yield new Affine(0, 1);
                    Affine paramAffine = paramAffines.get(sym);
                    if (paramAffine != null) yield paramAffine;
                    if (sym == null) yield null;
                    yield new Affine(getValue(sym, frame), 0);
                }
                case UnaryExpr ue -> {
                    Affine a = evalAffineWithParams(ue.operand(), loopSym, frame, paramAffines);
                    if (a == null) yield null;
                    yield switch (ue.op()) {
                        case "+" -> a;
                        case "-" -> new Affine(-a.constant, -a.coefficient);
                        default -> null;
                    };
                }
                case BinaryExpr be -> {
                    Affine l = evalAffineWithParams(be.left(), loopSym, frame, paramAffines);
                    Affine r = evalAffineWithParams(be.right(), loopSym, frame, paramAffines);
                    if (l == null || r == null) yield null;
                    yield switch (be.op()) {
                        case "+" -> new Affine(l.constant + r.constant, l.coefficient + r.coefficient);
                        case "-" -> new Affine(l.constant - r.constant, l.coefficient - r.coefficient);
                        case "*" -> {
                            if (l.coefficient == 0) {
                                yield new Affine(l.constant * r.constant, l.constant * r.coefficient);
                            }
                            if (r.coefficient == 0) {
                                yield new Affine(l.constant * r.constant, l.coefficient * r.constant);
                            }
                            yield null;
                        }
                        default -> null;
                    };
                }
                default -> null;
            };
        }

        private Integer parseSelfStep(Expr expr, Symbol loopSym, EvalFrame frame) {
            if (!(expr instanceof BinaryExpr be)) return null;
            if (isIdOf(be.left(), loopSym) && !exprUsesSymbol(be.right(), loopSym)) {
                int delta = evalExpr(be.right(), frame);
                return switch (be.op()) {
                    case "+" -> delta;
                    case "-" -> -delta;
                    default -> null;
                };
            }
            if ("+".equals(be.op()) && isIdOf(be.right(), loopSym)
                    && !exprUsesSymbol(be.left(), loopSym)) {
                return evalExpr(be.left(), frame);
            }
            return null;
        }

        private long countIterations(int start, int bound, int step, String op) {
            if (step > 0) {
                long distance = switch (op) {
                    case "<" -> (long) bound - start;
                    case "<=" -> (long) bound - start + 1L;
                    case "!=" -> {
                        long diff = (long) bound - start;
                        yield diff > 0 && diff % step == 0 ? diff : -1L;
                    }
                    default -> -1L;
                };
                if (distance <= 0) return 0;
                return (distance + step - 1L) / step;
            }
            long posStep = -(long) step;
            long distance = switch (op) {
                case ">" -> (long) start - bound;
                case ">=" -> (long) start - bound + 1L;
                case "!=" -> {
                    long diff = (long) start - bound;
                    yield diff > 0 && diff % posStep == 0 ? diff : -1L;
                }
                default -> -1L;
            };
            if (distance <= 0) return 0;
            return (distance + posStep - 1L) / posStep;
        }

        private long arithmeticSeries(int start, int step, long n) {
            return n * (2L * start + (n - 1L) * step) / 2L;
        }

        private long squareSeries(int start, int step, long n) {
            long sumK = n * (n - 1L) / 2L;
            long sumK2 = n * (n - 1L) * (2L * n - 1L) / 6L;
            return n * (long) start * start
                    + 2L * start * step * sumK
                    + (long) step * step * sumK2;
        }

        private boolean isIdOf(Expr expr, Symbol sym) {
            return expr instanceof IdExpr id && analyzer.getIdSymbols().get(id) == sym;
        }

        private boolean exprUsesSymbol(Expr expr, Symbol sym) {
            return switch (expr) {
                case IdExpr id -> analyzer.getIdSymbols().get(id) == sym;
                case BinaryExpr be -> exprUsesSymbol(be.left(), sym) || exprUsesSymbol(be.right(), sym);
                case UnaryExpr ue -> exprUsesSymbol(ue.operand(), sym);
                case CallExpr ce -> {
                    for (Expr arg : ce.args()) if (exprUsesSymbol(arg, sym)) yield true;
                    yield false;
                }
                default -> false;
            };
        }

        private boolean exprUsesAnySymbol(Expr expr, Set<Symbol> symbols, Symbol ignored) {
            if (symbols.isEmpty()) return false;
            return switch (expr) {
                case IdExpr id -> {
                    Symbol sym = analyzer.getIdSymbols().get(id);
                    yield sym != null && sym != ignored && symbols.contains(sym);
                }
                case BinaryExpr be -> exprUsesAnySymbol(be.left(), symbols, ignored)
                        || exprUsesAnySymbol(be.right(), symbols, ignored);
                case UnaryExpr ue -> exprUsesAnySymbol(ue.operand(), symbols, ignored);
                case CallExpr ce -> {
                    boolean found = false;
                    for (Expr arg : ce.args()) {
                        if (exprUsesAnySymbol(arg, symbols, ignored)) {
                            found = true;
                            break;
                        }
                    }
                    yield found;
                }
                default -> false;
            };
        }

        private void collectAssignedNames(Stmt stmt, Set<String> out) {
            switch (stmt) {
                case Block b -> {
                    for (Stmt s : b.stmts()) collectAssignedNames(s, out);
                }
                case AssignStmt as_ -> out.add(as_.name());
                case VarDecl vd -> out.add(vd.name());
                case ConstDecl cd -> out.add(cd.name());
                case IfStmt is -> {
                    collectAssignedNames(is.thenStmt(), out);
                    if (is.elseStmt() != null) collectAssignedNames(is.elseStmt(), out);
                }
                case WhileStmt ws -> collectAssignedNames(ws.body(), out);
                default -> {}
            }
        }

        private boolean exprUsesAnyName(Expr expr, Set<String> names, String ignored) {
            if (names.isEmpty()) return false;
            return switch (expr) {
                case IdExpr id -> !id.name().equals(ignored) && names.contains(id.name());
                case BinaryExpr be -> exprUsesAnyName(be.left(), names, ignored)
                        || exprUsesAnyName(be.right(), names, ignored);
                case UnaryExpr ue -> exprUsesAnyName(ue.operand(), names, ignored);
                case CallExpr ce -> {
                    boolean found = false;
                    for (Expr arg : ce.args()) {
                        if (exprUsesAnyName(arg, names, ignored)) {
                            found = true;
                            break;
                        }
                    }
                    yield found;
                }
                default -> false;
            };
        }

        private int getValue(Symbol sym, EvalFrame frame) {
            if (sym.isConst() && sym.getConstValue() != null) return sym.getConstValue();
            Integer value = sym.isGlobal() ? globals.get(sym) : frame.locals.get(sym);
            if (value == null) throw new ConstEvalBailout();
            return value;
        }

        private void setValue(Symbol sym, int value, EvalFrame frame) {
            if (sym.isGlobal()) globals.put(sym, value);
            else frame.locals.put(sym, value);
        }
    }

    private static final class EvalFrame {
        final IdentityHashMap<Symbol, Integer> locals = new IdentityHashMap<>();
        final FuncDef func;

        EvalFrame() {
            this(null);
        }

        EvalFrame(FuncDef func) {
            this.func = func;
        }
    }

    private record Affine(int constant, int coefficient) {}
    private record Poly(int constant, int linear, int quadratic) {
        Poly add(Poly other) {
            return new Poly(constant + other.constant, linear + other.linear, quadratic + other.quadratic);
        }

        Poly subtract(Poly other) {
            return new Poly(constant - other.constant, linear - other.linear, quadratic - other.quadratic);
        }

        Poly negate() {
            return new Poly(-constant, -linear, -quadratic);
        }

        Poly multiply(Poly other) {
            int degree = (quadratic != 0 ? 2 : linear != 0 ? 1 : 0)
                    + (other.quadratic != 0 ? 2 : other.linear != 0 ? 1 : 0);
            if (degree > 2) return null;
            int c = constant * other.constant;
            int l = constant * other.linear + linear * other.constant;
            int q = constant * other.quadratic + linear * other.linear + quadratic * other.constant;
            return new Poly(c, l, q);
        }

        int eval(int x) {
            return constant + linear * x + quadratic * x * x;
        }
    }
    private record LoopUpdate(Symbol target, int constant, int coefficient, int quadratic) {}
    private record CountedLoopInfo(Symbol loopSym, List<Stmt> stmts, int start, int step, long iterations) {}
    private record LoopGuard(IdExpr loopId, Expr boundExpr, String continueOp) {}
    private sealed interface BulkLoopStmt permits BulkUpdates, BulkIf {}
    private record BulkUpdates(List<LoopUpdate> updates) implements BulkLoopStmt {}
    private record BulkIf(BulkCond cond, List<LoopUpdate> thenUpdates,
                          List<LoopUpdate> elseUpdates) implements BulkLoopStmt {}
    private sealed interface BulkCond permits BulkModuloCond, BulkRelCond {}
    private record BulkModuloCond(int modulus, int remainder, boolean negate) implements BulkCond {}
    private record BulkRelCond(String op, int bound) implements BulkCond {}
    private record ModuloExpr(int modulus) {}
    private record CountAndSum(long count, long sum) {}
    private record CallKey(String funcName, int[] args) {
        CallKey(String funcName, List<Integer> values) {
            this(funcName, values.stream().mapToInt(Integer::intValue).toArray());
        }

        @Override
        public boolean equals(Object obj) {
            return obj instanceof CallKey other
                    && funcName.equals(other.funcName)
                    && Arrays.equals(args, other.args);
        }

        @Override
        public int hashCode() {
            return 31 * funcName.hashCode() + Arrays.hashCode(args);
        }
    }

    private static class FastSignal extends RuntimeException {
        @Override
        public synchronized Throwable fillInStackTrace() {
            return this;
        }
    }

    private static class ConstEvalBailout extends FastSignal {}
    private static final class BreakSignal extends FastSignal {}
    private static final class ContinueSignal extends FastSignal {}
    private static final class TailCallSignal extends FastSignal {
        final List<Integer> args;
        TailCallSignal(List<Integer> args) { this.args = args; }
    }
    private static final class ReturnSignal extends FastSignal {
        final int value;
        ReturnSignal(int value) { this.value = value; }
    }

    // ========== Function definition ==========

    private void genFuncDef(FuncDef fd) {
        currentFunc = fd;
        currentFuncBodyLabel = newLabel("func_body_" + fd.name());
        localOffsetStack.clear();
        localOffsetStack.push(new HashMap<>()); // function scope
        freeSpillSlots.clear();
        varRegCache.clear();
        regToVar.clear();
        varDirty.clear();
        lastStoreReg.clear();
        regValid.clear();
        symbolRegs.clear();
        globalAddrRegs.clear();
        Arrays.fill(tempUsed, false);
        Arrays.fill(aUsed, false);
        codegenLoopDepth = 0;
        nextLocalOffset = -8; // skip past saved ra (-4) and saved fp (-8)

        // Count locals declared in the body
        countLocals(fd.body());

        // Determine whether this is a leaf function (no calls in body)
        // and whether parameters can be kept in a0-a7 registers.
        boolean isLeaf = !stmtContainsCall(fd.body());
        currentFuncIsLeaf = isLeaf;

        Symbol funcSym = analyzer.getFuncSymbols().get(fd);
        assignSavedRegisters(fd);
        assignGlobalAddressRegisters(fd);
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
        int savedAddrRegCount = globalAddrRegs.size();
        int savedCalleeRegCount = savedValueRegCount + savedAddrRegCount;
        boolean hasLocalsOrParams = finalLocalOffset < -8;
        boolean needsFrame = hasLocalsOrParams || maxSpillDepth > 0;
        if (savedCalleeRegCount > 0) {
            needsFrame = true;
        }

        // Calculate frame size.
        int savedRegsSize = (needsFrame || !isLeaf) ? 8 + savedCalleeRegCount * 4 : 0;

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
            for (int i = 0; i < savedCalleeRegCount; i++) {
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
        for (Map.Entry<Symbol, String> entry : globalAddrRegs.entrySet()) {
            emit("la", entry.getValue(), entry.getKey().getName());
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
        emitLabel(currentFuncBodyLabel);
        genStmt(fd.body());

        // Epilogue
        emitLabel(funcEpilogueLabel());
        if (frameSize > 0) {
            if (!isLeaf) {
                emit("lw", "ra", (frameSize - 4) + "(sp)");
            }
            for (int i = 0; i < savedCalleeRegCount; i++) {
                emit("lw", SAVED_VALUE_REGS[i], (frameSize - 12 - i * 4) + "(sp)");
            }
            emit("lw", "s0", (frameSize - 8) + "(sp)");
            emit("addi", "sp", "sp", String.valueOf(frameSize));
        }
        emit("ret");

        currentFunc = null;
        currentFuncBodyLabel = null;
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
        boolean tailRecursive = containsTailRecursiveReturn(fd.body(), fd.name());

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
            if (entry.getValue() < (tailRecursive ? 2 : 8)) continue;
            candidates.add(entry);
        }
        candidates.sort((a, b) -> Integer.compare(b.getValue(), a.getValue()));

        int n = Math.min(SAVED_VALUE_REGS.length, candidates.size());
        for (int i = 0; i < n; i++) {
            symbolRegs.put(candidates.get(i).getKey(), SAVED_VALUE_REGS[i]);
        }
    }

    private void assignGlobalAddressRegisters(FuncDef fd) {
        if (!optimize || !enableGlobalAddrCache) return;

        int base = symbolRegs.size();
        if (base >= SAVED_VALUE_REGS.length) return;

        IdentityHashMap<Symbol, Integer> weights = new IdentityHashMap<>();
        collectGlobalAccessWeights(fd.body(), weights, 0);

        List<Map.Entry<Symbol, Integer>> candidates = new ArrayList<>();
        for (Map.Entry<Symbol, Integer> entry : weights.entrySet()) {
            Symbol sym = entry.getKey();
            if (sym == null || !sym.isGlobal() || sym.isConst() || sym.isFunc()) continue;
            if (entry.getValue() < 8) continue;
            candidates.add(entry);
        }
        candidates.sort((a, b) -> {
            int byWeight = Integer.compare(b.getValue(), a.getValue());
            if (byWeight != 0) return byWeight;
            return a.getKey().getName().compareTo(b.getKey().getName());
        });

        int n = Math.min(SAVED_VALUE_REGS.length - base, candidates.size());
        for (int i = 0; i < n; i++) {
            globalAddrRegs.put(candidates.get(i).getKey(), SAVED_VALUE_REGS[base + i]);
        }
    }

    private void collectGlobalAccessWeights(Stmt stmt, IdentityHashMap<Symbol, Integer> weights, int loopDepth) {
        switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) {
                    collectGlobalAccessWeights(s, weights, loopDepth);
                }
            }
            case ExprStmt es -> collectGlobalExprWeights(es.expr(), weights, loopDepth);
            case AssignStmt as_ -> {
                Symbol target = analyzer.getAssignSymbols().get(as_);
                if (target != null && target.isGlobal() && !target.isConst()) {
                    weights.merge(target, weightFor(loopDepth) + 2, Integer::sum);
                }
                collectGlobalExprWeights(as_.value(), weights, loopDepth);
            }
            case VarDecl vd -> collectGlobalExprWeights(vd.initExpr(), weights, loopDepth);
            case ConstDecl cd -> collectGlobalExprWeights(cd.initExpr(), weights, loopDepth);
            case IfStmt is -> {
                collectGlobalExprWeights(is.condition(), weights, loopDepth);
                collectGlobalAccessWeights(is.thenStmt(), weights, loopDepth);
                if (is.elseStmt() != null) collectGlobalAccessWeights(is.elseStmt(), weights, loopDepth);
            }
            case WhileStmt ws -> {
                collectGlobalExprWeights(ws.condition(), weights, loopDepth + 1);
                collectGlobalAccessWeights(ws.body(), weights, loopDepth + 1);
            }
            case ReturnStmt rs -> {
                if (rs.value() != null) collectGlobalExprWeights(rs.value(), weights, loopDepth);
            }
            default -> {}
        }
    }

    private void collectGlobalExprWeights(Expr expr, IdentityHashMap<Symbol, Integer> weights, int loopDepth) {
        switch (expr) {
            case IdExpr id -> {
                Symbol sym = analyzer.getIdSymbols().get(id);
                if (sym != null && sym.isGlobal() && !sym.isConst()) {
                    weights.merge(sym, weightFor(loopDepth), Integer::sum);
                }
            }
            case BinaryExpr be -> {
                collectGlobalExprWeights(be.left(), weights, loopDepth);
                collectGlobalExprWeights(be.right(), weights, loopDepth);
            }
            case UnaryExpr ue -> collectGlobalExprWeights(ue.operand(), weights, loopDepth);
            case CallExpr ce -> {
                for (Expr arg : ce.args()) collectGlobalExprWeights(arg, weights, loopDepth);
            }
            default -> {}
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

    private boolean containsTailRecursiveReturn(Stmt stmt, String funcName) {
        return switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) {
                    if (containsTailRecursiveReturn(s, funcName)) yield true;
                }
                yield false;
            }
            case IfStmt is -> containsTailRecursiveReturn(is.thenStmt(), funcName)
                    || (is.elseStmt() != null && containsTailRecursiveReturn(is.elseStmt(), funcName));
            case WhileStmt ws -> containsTailRecursiveReturn(ws.body(), funcName);
            case ReturnStmt rs -> rs.value() instanceof CallExpr ce && ce.funcName().equals(funcName);
            default -> false;
        };
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
                if (ce.args().size() > NUM_TEMPS) {
                    yield maxD + ce.args().size();
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
                List<Stmt> stmts = b.stmts();
                List<Set<Symbol>> suffixUses = buildSuffixUses(stmts);
                for (int i = 0; i < stmts.size(); i++) {
                    Stmt s = stmts.get(i);
                    if (s instanceof VarDecl vd) blockVars.add(vd.name());
                    else if (s instanceof ConstDecl cd) blockVars.add(cd.name());
                    if (enableBlockDce && optimize && codegenLoopDepth == 0
                            && isDeadForLiveOut(s, suffixUses.get(i + 1))) {
                        if (s instanceof VarDecl vd) allocateLocal(vd.name());
                        else if (s instanceof ConstDecl cd) allocateLocal(cd.name());
                        continue;
                    }
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
                    Symbol sym = targetSym;
                    if (sym != null && sym.isGlobal() && !sym.isConst()) {
                        // Store to global variable
                        String addrReg = globalAddrRegs.get(sym);
                        if (addrReg != null) {
                            emit("sw", r, "0(" + addrReg + ")");
                        } else {
                            addrReg = allocReg();
                            emit("la", addrReg, sym.getName());
                            emit("sw", r, "0(" + addrReg + ")");
                            freeReg(addrReg);
                        }
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

        genBranchIfFalse(is.condition(), is.elseStmt() != null ? elseLabel : endLabel);

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
        genBranchIfFalse(ws.condition(), endLabel);

        emitLabel(bodyLabel);
        codegenLoopDepth++;
        genStmt(ws.body());
        codegenLoopDepth--;
        emit("j", startLabel);

        emitLabel(endLabel);
        loopStack.pop();
    }

    private void genReturn(ReturnStmt rs) {
        flushAllDirty();
        if (rs.value() != null) {
            if (optimize && tryEmitTailRecursiveReturn(rs.value())) {
                return;
            }
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

    private void genBranchIfFalse(Expr expr, String label) {
        if (expr instanceof UnaryExpr ue && "!".equals(ue.op())) {
            genBranchIfTrue(ue.operand(), label);
            return;
        }
        if (expr instanceof BinaryExpr be) {
            if ("&&".equals(be.op())) {
                genBranchIfFalse(be.left(), label);
                genBranchIfFalse(be.right(), label);
                return;
            }
            if ("||".equals(be.op())) {
                String endLabel = newLabel("lor_true");
                genBranchIfTrue(be.left(), endLabel);
                genBranchIfFalse(be.right(), label);
                emitLabel(endLabel);
                return;
            }
            if (isCompareOp(be.op()) && !exprContainsCall(be.left()) && !exprContainsCall(be.right())) {
                emitCompareBranch(be.op(), false, be.left(), be.right(), label);
                return;
            }
        }

        BranchOperand operand = branchOperand(expr);
        emit("beqz", operand.reg, label);
        freeBranchOperand(operand);
    }

    private void genBranchIfTrue(Expr expr, String label) {
        if (expr instanceof UnaryExpr ue && "!".equals(ue.op())) {
            genBranchIfFalse(ue.operand(), label);
            return;
        }
        if (expr instanceof BinaryExpr be) {
            if ("&&".equals(be.op())) {
                String falseLabel = newLabel("land_false");
                genBranchIfFalse(be.left(), falseLabel);
                genBranchIfTrue(be.right(), label);
                emitLabel(falseLabel);
                return;
            }
            if ("||".equals(be.op())) {
                genBranchIfTrue(be.left(), label);
                genBranchIfTrue(be.right(), label);
                return;
            }
            if (isCompareOp(be.op()) && !exprContainsCall(be.left()) && !exprContainsCall(be.right())) {
                emitCompareBranch(be.op(), true, be.left(), be.right(), label);
                return;
            }
        }

        BranchOperand operand = branchOperand(expr);
        emit("bnez", operand.reg, label);
        freeBranchOperand(operand);
    }

    private boolean isCompareOp(String op) {
        return "==".equals(op) || "!=".equals(op) || "<".equals(op)
                || ">".equals(op) || "<=".equals(op) || ">=".equals(op);
    }

    private void emitCompareBranch(String op, boolean branchOnTrue, Expr left, Expr right, String label) {
        BranchOperand lOp = branchOperand(left);
        BranchOperand rOp = branchOperand(right);
        String l = lOp.reg;
        String r = rOp.reg;

        if (branchOnTrue) {
            switch (op) {
                case "==" -> emit("beq", l, r, label);
                case "!=" -> emit("bne", l, r, label);
                case "<" -> emit("blt", l, r, label);
                case ">" -> emit("blt", r, l, label);
                case "<=" -> emit("bge", r, l, label);
                case ">=" -> emit("bge", l, r, label);
                default -> {}
            }
        } else {
            switch (op) {
                case "==" -> emit("bne", l, r, label);
                case "!=" -> emit("beq", l, r, label);
                case "<" -> emit("bge", l, r, label);
                case ">" -> emit("bge", r, l, label);
                case "<=" -> emit("blt", r, l, label);
                case ">=" -> emit("blt", l, r, label);
                default -> {}
            }
        }

        freeBranchOperand(rOp);
        freeBranchOperand(lOp);
    }

    private BranchOperand branchOperand(Expr expr) {
        if (expr instanceof LiteralExpr le && le.value() == 0) {
            return new BranchOperand("zero", false);
        }
        if (expr instanceof IdExpr id) {
            Symbol sym = analyzer.getIdSymbols().get(id);
            if (sym != null) {
                if (sym.isConst() && sym.getConstValue() != null && sym.getConstValue() == 0) {
                    return new BranchOperand("zero", false);
                }
                String savedReg = symbolRegs.get(sym);
                if (savedReg != null) {
                    return new BranchOperand(savedReg, false);
                }
            }
        }
        return new BranchOperand(genExpr(expr), true);
    }

    private void freeBranchOperand(BranchOperand operand) {
        if (operand.owned) {
            freeReg(operand.reg);
        }
    }

    private List<Set<Symbol>> buildSuffixUses(List<Stmt> stmts) {
        List<Set<Symbol>> suffix = new ArrayList<>(Collections.nCopies(stmts.size() + 1, null));
        Set<Symbol> live = newIdentitySet();
        suffix.set(stmts.size(), newIdentitySet());
        for (int i = stmts.size() - 1; i >= 0; i--) {
            Set<Symbol> current = newIdentitySet();
            current.addAll(live);
            suffix.set(i + 1, current);

            removeAssignedLocals(live, stmts.get(i));
            collectUsedSymbols(stmts.get(i), live);
        }
        suffix.set(0, live);
        return suffix;
    }

    private boolean isDeadForLiveOut(Stmt stmt, Set<Symbol> liveOut) {
        if (stmt instanceof AssignStmt as_) {
            Symbol target = analyzer.getAssignSymbols().get(as_);
            return target != null && !target.isGlobal()
                    && !liveOut.contains(target)
                    && isPureExpr(as_.value());
        }
        if (stmt instanceof VarDecl vd) {
            Symbol target = analyzer.getVarDeclSymbols().get(vd);
            return target != null && !liveOut.contains(target) && isPureExpr(vd.initExpr());
        }
        if (stmt instanceof ConstDecl cd) {
            Symbol target = analyzer.getConstDeclSymbols().get(cd);
            return target != null && !liveOut.contains(target) && isPureExpr(cd.initExpr());
        }
        if (stmt instanceof WhileStmt ws) {
            if (!isPureExpr(ws.condition()) || stmtMayHaveSideEffects(ws.body())) return false;
            Set<Symbol> assigned = newIdentitySet();
            collectAssignedSymbols(ws.body(), assigned);
            for (Symbol sym : assigned) {
                if (liveOut.contains(sym)) return false;
            }
            return true;
        }
        return false;
    }

    private void removeAssignedLocals(Set<Symbol> symbols, Stmt stmt) {
        Set<Symbol> assigned = newIdentitySet();
        collectAssignedSymbols(stmt, assigned);
        for (Symbol sym : assigned) {
            if (!sym.isGlobal()) symbols.remove(sym);
        }
    }

    private void collectUsedSymbols(Stmt stmt, Set<Symbol> out) {
        switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) collectUsedSymbols(s, out);
            }
            case ExprStmt es -> collectUsedSymbols(es.expr(), out);
            case AssignStmt as_ -> collectUsedSymbols(as_.value(), out);
            case VarDecl vd -> collectUsedSymbols(vd.initExpr(), out);
            case ConstDecl cd -> collectUsedSymbols(cd.initExpr(), out);
            case IfStmt is -> {
                collectUsedSymbols(is.condition(), out);
                collectUsedSymbols(is.thenStmt(), out);
                if (is.elseStmt() != null) collectUsedSymbols(is.elseStmt(), out);
            }
            case WhileStmt ws -> {
                collectUsedSymbols(ws.condition(), out);
                collectUsedSymbols(ws.body(), out);
            }
            case ReturnStmt rs -> {
                if (rs.value() != null) collectUsedSymbols(rs.value(), out);
            }
            default -> {}
        }
    }

    private void collectUsedSymbols(Expr expr, Set<Symbol> out) {
        switch (expr) {
            case IdExpr id -> {
                Symbol sym = analyzer.getIdSymbols().get(id);
                if (sym != null) out.add(sym);
            }
            case BinaryExpr be -> {
                collectUsedSymbols(be.left(), out);
                collectUsedSymbols(be.right(), out);
            }
            case UnaryExpr ue -> collectUsedSymbols(ue.operand(), out);
            case CallExpr ce -> {
                for (Expr arg : ce.args()) collectUsedSymbols(arg, out);
            }
            default -> {}
        }
    }

    private void collectAssignedSymbols(Stmt stmt, Set<Symbol> out) {
        switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) collectAssignedSymbols(s, out);
            }
            case AssignStmt as_ -> {
                Symbol sym = analyzer.getAssignSymbols().get(as_);
                if (sym != null) out.add(sym);
            }
            case VarDecl vd -> {
                Symbol sym = analyzer.getVarDeclSymbols().get(vd);
                if (sym != null) out.add(sym);
            }
            case ConstDecl cd -> {
                Symbol sym = analyzer.getConstDeclSymbols().get(cd);
                if (sym != null) out.add(sym);
            }
            case IfStmt is -> {
                collectAssignedSymbols(is.thenStmt(), out);
                if (is.elseStmt() != null) collectAssignedSymbols(is.elseStmt(), out);
            }
            case WhileStmt ws -> collectAssignedSymbols(ws.body(), out);
            default -> {}
        }
    }

    private boolean stmtMayHaveSideEffects(Stmt stmt) {
        return switch (stmt) {
            case Block b -> {
                boolean result = false;
                for (Stmt s : b.stmts()) {
                    if (stmtMayHaveSideEffects(s)) {
                        result = true;
                        break;
                    }
                }
                yield result;
            }
            case ExprStmt es -> !isPureExpr(es.expr());
            case AssignStmt as_ -> {
                Symbol sym = analyzer.getAssignSymbols().get(as_);
                yield sym == null || sym.isGlobal() || !isPureExpr(as_.value());
            }
            case VarDecl vd -> !isPureExpr(vd.initExpr());
            case ConstDecl cd -> !isPureExpr(cd.initExpr());
            case IfStmt is -> !isPureExpr(is.condition())
                    || stmtMayHaveSideEffects(is.thenStmt())
                    || (is.elseStmt() != null && stmtMayHaveSideEffects(is.elseStmt()));
            case WhileStmt ws -> !isPureExpr(ws.condition()) || stmtMayHaveSideEffects(ws.body());
            case ReturnStmt ignored -> true;
            default -> false;
        };
    }

    private Set<Symbol> newIdentitySet() {
        return Collections.newSetFromMap(new IdentityHashMap<>());
    }

    private boolean tryEmitTailRecursiveReturn(Expr value) {
        if (!(value instanceof CallExpr ce)) return false;
        if (currentFunc == null || !currentFunc.name().equals(ce.funcName())) return false;

        List<Symbol> paramSymbols = analyzer.getFuncParamSymbols().get(currentFunc);
        if (paramSymbols == null || ce.args().size() != paramSymbols.size()) return false;

        clearCallerSavedStateBeforeCall();

        if (ce.args().size() <= NUM_TEMPS && !callArgsContainCall(ce)) {
            String[] argRegs = new String[ce.args().size()];
            for (int i = 0; i < ce.args().size(); i++) {
                argRegs[i] = genExpr(ce.args().get(i));
            }
            assignTailArgsToParams(paramSymbols, argRegs);
            emit("j", currentFuncBodyLabel);
            return true;
        }

        int[] argSlots = new int[ce.args().size()];
        for (int i = 0; i < ce.args().size(); i++) {
            String r = genExpr(ce.args().get(i));
            int slot = allocateSpillSlot();
            spillReg(r, slot);
            freeReg(r);
            argSlots[i] = slot;
        }

        Symbol funcSym = analyzer.getFuncSymbols().get(currentFunc);
        List<String> paramNames = funcSym != null ? funcSym.getFuncParamNames() : null;
        for (int i = 0; i < paramSymbols.size(); i++) {
            Symbol paramSym = paramSymbols.get(i);
            String savedReg = symbolRegs.get(paramSym);
            if (savedReg != null) {
                emit("lw", savedReg, argSlots[i] + "(s0)");
                freeSpillSlot(argSlots[i]);
                continue;
            }

            String r = loadSpill(argSlots[i]);
            freeSpillSlot(argSlots[i]);
            String paramName = paramNames != null ? paramNames.get(i) : paramSym.getName();
            int offset = getLocalOffset(paramName);
            emit("sw", r, offset + "(s0)");
            freeReg(r);
        }

        emit("j", currentFuncBodyLabel);
        return true;
    }

    private boolean callArgsContainCall(CallExpr ce) {
        for (Expr arg : ce.args()) {
            if (exprContainsCall(arg)) return true;
        }
        return false;
    }

    private void assignTailArgsToParams(List<Symbol> paramSymbols, String[] argRegs) {
        Symbol funcSym = analyzer.getFuncSymbols().get(currentFunc);
        List<String> paramNames = funcSym != null ? funcSym.getFuncParamNames() : null;

        for (int i = 0; i < paramSymbols.size(); i++) {
            Symbol paramSym = paramSymbols.get(i);
            String savedReg = symbolRegs.get(paramSym);
            if (savedReg != null) {
                if (!savedReg.equals(argRegs[i])) {
                    emit("mv", savedReg, argRegs[i]);
                }
            } else {
                String paramName = paramNames != null ? paramNames.get(i) : paramSym.getName();
                int offset = getLocalOffset(paramName);
                emit("sw", argRegs[i], offset + "(s0)");
            }
            freeReg(argRegs[i]);
        }
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
            // Load from global address. Hot globals keep their address in s-regs.
            String addrReg = globalAddrRegs.get(sym);
            if (addrReg != null) {
                emit("lw", r, "0(" + addrReg + ")");
            } else {
                emit("la", r, sym.getName());
                emit("lw", r, "0(" + r + ")");
            }
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
            case CallExpr ce -> !canInlineCall(ce);
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
        if (optimize && enableSmallFunctionInline) {
            String inlined = tryGenInlineCall(ce);
            if (inlined != null) return inlined;
        }

        if (ce.args().size() > NUM_TEMPS) {
            return genLargeCall(ce);
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

    private String tryGenInlineCall(CallExpr ce) {
        if (!canInlineCall(ce)) return null;

        FuncDef fd = functionsByName.get(ce.funcName());
        Expr returnExpr = singleReturnExpr(fd.body());
        List<Symbol> params = analyzer.getFuncParamSymbols().get(fd);

        String[] argRegs = new String[ce.args().size()];
        for (int i = 0; i < ce.args().size(); i++) {
            argRegs[i] = genExpr(ce.args().get(i));
        }

        IdentityHashMap<Symbol, String> paramRegs = new IdentityHashMap<>();
        for (int i = 0; i < params.size(); i++) {
            paramRegs.put(params.get(i), argRegs[i]);
        }
        String result = genInlineExpr(returnExpr, paramRegs);
        for (String argReg : argRegs) {
            freeReg(argReg);
        }
        return result;
    }

    private Expr singleReturnExpr(Stmt stmt) {
        if (stmt instanceof ReturnStmt rs) return rs.value();
        if (stmt instanceof Block b && b.stmts().size() == 1 && b.stmts().get(0) instanceof ReturnStmt rs) {
            return rs.value();
        }
        return null;
    }

    private boolean canInlineCall(CallExpr ce) {
        if (!optimize || !enableSmallFunctionInline) return false;
        FuncDef fd = functionsByName.get(ce.funcName());
        if (fd == null || fd == currentFunc) return false;
        Expr returnExpr = singleReturnExpr(fd.body());
        if (returnExpr == null || !isInlineExpr(returnExpr) || containsShortCircuit(returnExpr)) return false;
        List<Symbol> params = analyzer.getFuncParamSymbols().get(fd);
        if (params == null || params.size() != ce.args().size() || params.size() > 6) return false;
        for (Expr arg : ce.args()) {
            if (exprHasCallRaw(arg)) return false;
        }
        return true;
    }

    private boolean isInlineExpr(Expr expr) {
        return switch (expr) {
            case LiteralExpr ignored -> true;
            case IdExpr ignored -> true;
            case UnaryExpr ue -> isInlineExpr(ue.operand());
            case BinaryExpr be -> isInlineExpr(be.left()) && isInlineExpr(be.right());
            case CallExpr ignored -> false;
        };
    }

    private boolean containsShortCircuit(Expr expr) {
        return switch (expr) {
            case BinaryExpr be -> "&&".equals(be.op()) || "||".equals(be.op())
                    || containsShortCircuit(be.left()) || containsShortCircuit(be.right());
            case UnaryExpr ue -> containsShortCircuit(ue.operand());
            case CallExpr ce -> true;
            default -> false;
        };
    }

    private boolean exprHasCallRaw(Expr expr) {
        return switch (expr) {
            case CallExpr ignored -> true;
            case BinaryExpr be -> exprHasCallRaw(be.left()) || exprHasCallRaw(be.right());
            case UnaryExpr ue -> exprHasCallRaw(ue.operand());
            default -> false;
        };
    }

    private String genInlineExpr(Expr expr, IdentityHashMap<Symbol, String> paramRegs) {
        return switch (expr) {
            case LiteralExpr le -> genLiteral(le);
            case IdExpr id -> {
                Symbol sym = analyzer.getIdSymbols().get(id);
                String paramReg = paramRegs.get(sym);
                if (paramReg != null) {
                    String r = allocReg();
                    emit("mv", r, paramReg);
                    yield r;
                }
                yield genId(id);
            }
            case UnaryExpr ue -> {
                String operand = genInlineExpr(ue.operand(), paramRegs);
                String result = allocReg();
                switch (ue.op()) {
                    case "+" -> emit("mv", result, operand);
                    case "-" -> emit("sub", result, "zero", operand);
                    case "!" -> emit("seqz", result, operand);
                    default -> emit("mv", result, operand);
                }
                freeReg(operand);
                yield result;
            }
            case BinaryExpr be -> {
                String left = genInlineExpr(be.left(), paramRegs);
                if (be.right() instanceof LiteralExpr rle && tryEmitRightLiteralOp(be.op(), left, rle.value())) {
                    yield left;
                }
                String right = genInlineExpr(be.right(), paramRegs);
                emitBinaryOp(be.op(), left, left, right);
                freeReg(right);
                yield left;
            }
            case CallExpr ce -> throw new IllegalStateException("inline call expression was pre-filtered");
        };
    }

    private String genLargeCall(CallExpr ce) {
        clearCallerSavedStateBeforeCall();

        int numArgs = ce.args().size();
        int regArgCount = Math.min(numArgs, 8);
        int[] argSpills = new int[numArgs];

        for (int i = 0; i < numArgs; i++) {
            String r = genExpr(ce.args().get(i));
            int slot = allocateSpillSlot();
            spillReg(r, slot);
            freeReg(r);
            argSpills[i] = slot;
        }

        for (int i = 0; i < regArgCount; i++) {
            emit("lw", "a" + i, argSpills[i] + "(s0)");
            freeSpillSlot(argSpills[i]);
        }

        int extraArgs = numArgs - 8;
        int extraAlignedSize = 0;
        if (extraArgs > 0) {
            int extraSize = extraArgs * 4;
            extraAlignedSize = (extraSize + 15) & ~15;
            emit("addi", "sp", "sp", String.valueOf(-extraAlignedSize));
            for (int i = 8; i < numArgs; i++) {
                String r = loadSpill(argSpills[i]);
                freeSpillSlot(argSpills[i]);
                emit("sw", r, ((i - 8) * 4) + "(sp)");
                freeReg(r);
            }
        }

        emit("call", ce.funcName());

        if (extraAlignedSize > 0) {
            emit("addi", "sp", "sp", String.valueOf(extraAlignedSize));
        }

        String resultReg = allocReg();
        emit("mv", resultReg, "a0");
        return resultReg;
    }

    private void clearCallerSavedStateBeforeCall() {
        if (optimize) {
            for (String reg : lastStoreReg.values()) {
                freeRegRaw(reg);
            }
            invalidateRegCache();
            lastStoreReg.clear();
            regValid.clear();
            for (int i = 0; i < NUM_A_REGS; i++) aUsed[i] = false;
        }
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
