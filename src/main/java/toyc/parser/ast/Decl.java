package toyc.parser.ast;

/**
 * Declaration nodes (also serve as statements inside blocks).
 */
public sealed interface Decl extends ASTNode, Stmt
        permits VarDecl, ConstDecl {
}
