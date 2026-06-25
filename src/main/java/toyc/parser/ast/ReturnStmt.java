package toyc.parser.ast;

/**
 * Return statement: return [expr] ;
 */
public record ReturnStmt(Expr value, int line) implements Stmt {
}
