package toyc.parser.ast;

/**
 * If statement: if (condition) thenStmt [else elseStmt]
 */
public record IfStmt(Expr condition, Stmt thenStmt, Stmt elseStmt) implements Stmt {
}
