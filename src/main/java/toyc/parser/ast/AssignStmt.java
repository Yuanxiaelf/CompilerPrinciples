package toyc.parser.ast;

/**
 * Assignment statement: id = expr ;
 */
public record AssignStmt(String name, Expr value, int line) implements Stmt {
}
