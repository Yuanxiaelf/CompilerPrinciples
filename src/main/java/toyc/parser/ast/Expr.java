package toyc.parser.ast;

/**
 * Expression nodes.
 */
public sealed interface Expr extends ASTNode
        permits BinaryExpr, UnaryExpr, LiteralExpr, IdExpr, CallExpr {
}
