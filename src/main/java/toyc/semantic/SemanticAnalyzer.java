package toyc.semantic;

import toyc.parser.ast.*;

import java.util.*;

/**
 * Semantic analyzer: builds symbol tables, resolves identifiers,
 * checks semantic constraints, and performs constant folding.
 */
public class SemanticAnalyzer {

    private SymbolTable globalScope;
    private SymbolTable currentScope;
    private final List<String> errors;

    // Annotations
    private final Map<Expr, Type> exprTypes = new HashMap<>();
    private final Map<IdExpr, Symbol> idSymbols = new HashMap<>();
    private final Map<FuncDef, Symbol> funcSymbols = new HashMap<>();

    // For tracking function return checking
    private String currentFuncReturnType;

    // For tracking loop depth (break/continue validation)
    private int loopDepth;
    // Stack of loop labels for break/continue
    private final Deque<LoopLabels> loopStack = new ArrayDeque<>();

    private record LoopLabels(String startLabel, String endLabel) {}

    public SemanticAnalyzer() {
        this.errors = new ArrayList<>();
    }

    public List<String> getErrors() { return errors; }
    public boolean hasErrors() { return !errors.isEmpty(); }
    public Map<Expr, Type> getExprTypes() { return exprTypes; }
    public Map<IdExpr, Symbol> getIdSymbols() { return idSymbols; }
    public Map<FuncDef, Symbol> getFuncSymbols() { return funcSymbols; }
    public SymbolTable getGlobalScope() { return globalScope; }

    // ========== Entry point ==========

    public void analyze(CompUnit compUnit) {
        globalScope = new SymbolTable();
        currentScope = globalScope;

        // Process all top-level items
        for (ASTNode item : compUnit.items()) {
            switch (item) {
                case FuncDef fd -> analyzeFuncDef(fd);
                case VarDecl vd -> analyzeGlobalVarDecl(vd);
                case ConstDecl cd -> analyzeGlobalConstDecl(cd);
                default -> error(item, "unexpected top-level node");
            }
        }

        // Check that main function exists
        Symbol mainSym = globalScope.lookup("main");
        if (mainSym == null || !mainSym.isFunc()) {
            error("program must contain a 'main' function returning int");
        } else if (!"int".equals(mainSym.getFuncReturnType())) {
            error("'main' function must return int");
        } else if (mainSym.getFuncParamNames() != null && !mainSym.getFuncParamNames().isEmpty()) {
            error("'main' function must have no parameters");
        }
    }

    // ========== Function definitions ==========

    private void analyzeFuncDef(FuncDef fd) {
        // Declare function in global scope
        List<String> paramNames = new ArrayList<>();
        for (Param p : fd.params()) {
            paramNames.add(p.name());
        }
        Symbol funcSym = new Symbol(fd.name(), fd.returnType(), paramNames, true);
        if (!globalScope.define(funcSym)) {
            error(fd, "duplicate function name '" + fd.name() + "'");
            return;
        }
        funcSymbols.put(fd, funcSym);

        // Enter function body scope
        currentFuncReturnType = fd.returnType();
        SymbolTable funcScope = new SymbolTable(globalScope);
        currentScope = funcScope;

        // Add parameters to function scope
        for (Param p : fd.params()) {
            Symbol paramSym = new Symbol(p.name(), Symbol.Kind.PARAM, Type.INT, false);
            if (!currentScope.define(paramSym)) {
                error(p, "duplicate parameter name '" + p.name() + "'");
            }
        }

        // Analyze body
        analyzeBlock(fd.body());

        // Check that int functions return on all paths
        if ("int".equals(fd.returnType())) {
            if (!allPathsReturn(fd.body())) {
                error(fd, "function '" + fd.name() + "' must return a value on all paths");
            }
        }

        // Restore scope
        currentScope = globalScope;
        currentFuncReturnType = null;
    }

    // ========== Global declarations ==========

    private void analyzeGlobalVarDecl(VarDecl vd) {
        Type t = analyzeExpr(vd.initExpr());
        if (t != Type.INT) {
            error(vd, "global variable initializer must have int type");
        }
        Symbol sym = new Symbol(vd.name(), Symbol.Kind.VAR, Type.INT, true);
        if (!globalScope.define(sym)) {
            error(vd, "duplicate global name '" + vd.name() + "'");
        }
    }

    private void analyzeGlobalConstDecl(ConstDecl cd) {
        // Const initializer must be compile-time evaluable
        Integer value = evalConst(cd.initExpr());
        if (value == null) {
            error(cd, "constant initializer must be a compile-time constant expression");
            return;
        }
        Symbol sym = new Symbol(cd.name(), Symbol.Kind.CONST, Type.INT, true);
        sym.setConstValue(value);
        if (!globalScope.define(sym)) {
            error(cd, "duplicate global name '" + cd.name() + "'");
        }
    }

    // ========== Statements ==========

    private void analyzeStmt(Stmt stmt) {
        switch (stmt) {
            case Block b -> analyzeBlock(b);
            case NullStmt ignored -> {}
            case ExprStmt es -> {
                Type t = analyzeExpr(es.expr());
                // OK as long as it's a valid expression (could be void function call, but
                // void calls are caught in analyzeExpr)
            }
            case AssignStmt as_ -> {
                Symbol sym = currentScope.lookup(as_.name());
                if (sym == null) {
                    error(as_, "undefined variable '" + as_.name() + "'");
                } else if (sym.isConst()) {
                    error(as_, "cannot assign to constant '" + as_.name() + "'");
                } else if (sym.isFunc()) {
                    error(as_, "'" + as_.name() + "' is a function, not a variable");
                }
                Type t = analyzeExpr(as_.value());
                if (t != Type.INT) {
                    error(as_, "assignment value must have int type");
                }
            }
            case VarDecl vd -> {
                Type t = analyzeExpr(vd.initExpr());
                if (t != Type.INT) {
                    error(vd, "variable initializer must have int type");
                }
                Symbol sym = new Symbol(vd.name(), Symbol.Kind.VAR, Type.INT, false);
                if (!currentScope.define(sym)) {
                    error(vd, "duplicate declaration of '" + vd.name() + "' in this scope");
                }
            }
            case ConstDecl cd -> {
                Integer value = evalConst(cd.initExpr());
                if (value == null) {
                    error(cd, "constant initializer must be a compile-time constant expression");
                    return;
                }
                Symbol sym = new Symbol(cd.name(), Symbol.Kind.CONST, Type.INT, false);
                sym.setConstValue(value);
                if (!currentScope.define(sym)) {
                    error(cd, "duplicate declaration of '" + cd.name() + "' in this scope");
                }
            }
            case IfStmt is -> {
                Type condType = analyzeExpr(is.condition());
                if (condType != Type.INT) {
                    error(is, "if condition must have int type");
                }
                analyzeStmt(is.thenStmt());
                if (is.elseStmt() != null) {
                    analyzeStmt(is.elseStmt());
                }
            }
            case WhileStmt ws -> {
                Type condType = analyzeExpr(ws.condition());
                if (condType != Type.INT) {
                    error(ws, "while condition must have int type");
                }
                loopDepth++;
                analyzeStmt(ws.body());
                loopDepth--;
            }
            case BreakStmt bs -> {
                if (loopDepth == 0) {
                    error(bs, "break statement outside of loop");
                }
            }
            case ContinueStmt cs -> {
                if (loopDepth == 0) {
                    error(cs, "continue statement outside of loop");
                }
            }
            case ReturnStmt rs -> {
                if ("void".equals(currentFuncReturnType)) {
                    if (rs.value() != null) {
                        error(rs, "void function cannot return a value");
                    }
                } else {
                    if (rs.value() == null) {
                        error(rs, "int function must return a value");
                    } else {
                        Type t = analyzeExpr(rs.value());
                        if (t != Type.INT) {
                            error(rs, "return value must have int type");
                        }
                    }
                }
            }
            default -> error(stmt, "unexpected statement type");
        }
    }

    private void analyzeBlock(Block block) {
        SymbolTable blockScope = new SymbolTable(currentScope);
        currentScope = blockScope;
        for (Stmt stmt : block.stmts()) {
            analyzeStmt(stmt);
        }
        currentScope = blockScope.getParent();
    }

    // ========== Expressions ==========

    /**
     * Analyze an expression, annotate its type, and return the type.
     */
    private Type analyzeExpr(Expr expr) {
        return switch (expr) {
            case LiteralExpr le -> {
                exprTypes.put(le, Type.INT);
                yield Type.INT;
            }
            case IdExpr id -> {
                Symbol sym = currentScope.lookup(id.name());
                if (sym == null) {
                    error(id, "undefined identifier '" + id.name() + "'");
                    exprTypes.put(id, Type.INT); // assume INT for error recovery
                    yield Type.INT;
                }
                idSymbols.put(id, sym);
                exprTypes.put(id, sym.getType());
                yield sym.getType();
            }
            case BinaryExpr be -> {
                Type lt = analyzeExpr(be.left());
                Type rt = analyzeExpr(be.right());

                // Division by zero check
                if (("/".equals(be.op()) || "%".equals(be.op())) &&
                        be.right() instanceof LiteralExpr rle && rle.value() == 0) {
                    error(be, "division by zero");
                }

                // All binary operators require INT operands
                if (lt != Type.INT || rt != Type.INT) {
                    error(be, "binary operator '" + be.op() + "' requires int operands");
                }
                exprTypes.put(be, Type.INT);
                yield Type.INT;
            }
            case UnaryExpr ue -> {
                Type ot = analyzeExpr(ue.operand());
                if (ot != Type.INT) {
                    error(ue, "unary operator '" + ue.op() + "' requires int operand");
                }
                exprTypes.put(ue, Type.INT);
                yield Type.INT;
            }
            case CallExpr ce -> {
                Symbol sym = globalScope.lookup(ce.funcName());
                if (sym == null || !sym.isFunc()) {
                    error(ce, "undefined function '" + ce.funcName() + "'");
                    exprTypes.put(ce, Type.INT);
                    yield Type.INT;
                }
                // Check argument count
                List<String> paramNames = sym.getFuncParamNames();
                int expected = paramNames != null ? paramNames.size() : 0;
                if (ce.args().size() != expected) {
                    error(ce, "function '" + ce.funcName() + "' expects " + expected +
                            " arguments but got " + ce.args().size());
                }
                // Analyze arguments
                for (Expr arg : ce.args()) {
                    Type at = analyzeExpr(arg);
                    if (at != Type.INT) {
                        error(arg, "function argument must have int type");
                    }
                }
                String retType = sym.getFuncReturnType();
                Type resultType = "int".equals(retType) ? Type.INT : Type.VOID;
                exprTypes.put(ce, resultType);
                yield resultType;
            }
        };
    }

    // ========== Constant evaluation ==========

    /**
     * Try to evaluate a compile-time constant expression.
     * Returns null if the expression cannot be evaluated at compile time.
     */
    public Integer evalConst(Expr expr) {
        return switch (expr) {
            case LiteralExpr le -> le.value();
            case IdExpr id -> {
                Symbol sym = currentScope.lookup(id.name());
                if (sym != null && sym.isConst()) {
                    yield sym.getConstValue();
                }
                yield null;
            }
            case BinaryExpr be -> {
                Integer l = evalConst(be.left());
                Integer r = evalConst(be.right());
                if (l == null || r == null) yield null;
                yield switch (be.op()) {
                    case "+" -> l + r;
                    case "-" -> l - r;
                    case "*" -> l * r;
                    case "/" -> {
                        if (r == 0) yield null;
                        yield l / r;
                    }
                    case "%" -> {
                        if (r == 0) yield null;
                        yield l % r;
                    }
                    case "==" -> l.equals(r) ? 1 : 0;
                    case "!=" -> l.equals(r) ? 0 : 1;
                    case "<" -> l < r ? 1 : 0;
                    case ">" -> l > r ? 1 : 0;
                    case "<=" -> l <= r ? 1 : 0;
                    case ">=" -> l >= r ? 1 : 0;
                    case "&&" -> (l != 0 && r != 0) ? 1 : 0;
                    case "||" -> (l != 0 || r != 0) ? 1 : 0;
                    default -> null;
                };
            }
            case UnaryExpr ue -> {
                Integer operand = evalConst(ue.operand());
                if (operand == null) yield null;
                yield switch (ue.op()) {
                    case "+" -> operand;
                    case "-" -> -operand;
                    case "!" -> (operand == 0) ? 1 : 0;
                    default -> null;
                };
            }
            case CallExpr ce -> null; // function calls are not compile-time constants
        };
    }

    // ========== Control flow analysis ==========

    /**
     * Check if a statement always returns (for all-paths-return analysis).
     */
    private boolean allPathsReturn(Stmt stmt) {
        return switch (stmt) {
            case Block b -> {
                for (Stmt s : b.stmts()) {
                    if (allPathsReturn(s)) yield true;
                }
                yield false;
            }
            case ReturnStmt ignored -> true;
            case IfStmt is -> {
                if (is.elseStmt() == null) yield false;
                yield allPathsReturn(is.thenStmt()) && allPathsReturn(is.elseStmt());
            }
            case WhileStmt ws -> {
                // A while loop body might not execute, so it doesn't guarantee return
                // unless we want to be more clever (like while(1) { return ... })
                yield false;
            }
            default -> false;
        };
    }

    // ========== Error helpers ==========

    private void error(ASTNode node, String msg) {
        int line = getLine(node);
        errors.add(String.format("Line %d: %s", line, msg));
    }

    private void error(String msg) {
        errors.add(msg);
    }

    private int getLine(ASTNode node) {
        return switch (node) {
            case VarDecl vd -> vd.line();
            case ConstDecl cd -> cd.line();
            case AssignStmt as_ -> as_.line();
            case ReturnStmt rs -> rs.line();
            case BreakStmt bs -> bs.line();
            case ContinueStmt cs -> cs.line();
            case BinaryExpr be -> be.line();
            case UnaryExpr ue -> ue.line();
            case LiteralExpr le -> le.line();
            case IdExpr id -> id.line();
            case CallExpr ce -> ce.line();
            case FuncDef fd -> {
                if (fd.params().isEmpty()) yield 0;
                yield 0; // approximate
            }
            default -> 0;
        };
    }
}
