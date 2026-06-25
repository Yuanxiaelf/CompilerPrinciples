package toyc.parser.ast;

/**
 * Expression statement: expr ;
 */
public record ExprStmt(Expr expr) implements Stmt {
}
