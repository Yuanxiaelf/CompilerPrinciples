package toyc.parser.ast;

/**
 * Root of the AST hierarchy.
 */
public sealed interface ASTNode
        permits CompUnit, FuncDef, Param, Decl, Stmt, Expr {
}
