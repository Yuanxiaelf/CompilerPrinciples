package toyc.parser.ast;

/**
 * Identifier reference expression.
 */
public record IdExpr(String name, int line) implements Expr {
}
