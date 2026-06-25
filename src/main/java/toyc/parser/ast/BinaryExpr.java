package toyc.parser.ast;

/**
 * Binary expression: left op right
 */
public record BinaryExpr(Expr left, String op, Expr right, int line) implements Expr {
}
