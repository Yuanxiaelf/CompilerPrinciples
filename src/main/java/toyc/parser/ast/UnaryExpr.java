package toyc.parser.ast;

/**
 * Unary expression: op operand
 */
public record UnaryExpr(String op, Expr operand, int line) implements Expr {
}
