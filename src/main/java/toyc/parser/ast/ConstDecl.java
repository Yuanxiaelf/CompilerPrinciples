package toyc.parser.ast;

/**
 * Constant declaration: const int name = expr;
 */
public record ConstDecl(String name, Expr initExpr, int line) implements Decl {
}
