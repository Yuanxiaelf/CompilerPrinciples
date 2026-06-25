package toyc.parser.ast;

/**
 * Integer literal expression.
 */
public record LiteralExpr(int value, int line) implements Expr {
}
