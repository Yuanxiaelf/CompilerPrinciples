package toyc.parser.ast;

/**
 * While statement: while (condition) body
 */
public record WhileStmt(Expr condition, Stmt body) implements Stmt {
}
