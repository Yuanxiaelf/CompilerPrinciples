package toyc.parser.ast;

/**
 * Statement nodes.
 */
public sealed interface Stmt extends ASTNode
        permits Block, Decl, NullStmt, ExprStmt, AssignStmt,
                IfStmt, WhileStmt, BreakStmt, ContinueStmt, ReturnStmt {
}
