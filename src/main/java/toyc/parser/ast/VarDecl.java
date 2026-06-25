package toyc.parser.ast;

/**
 * Variable declaration: int name = expr;
 */
public record VarDecl(String name, Expr initExpr, int line) implements Decl {
}
