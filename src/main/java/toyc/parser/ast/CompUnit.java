package toyc.parser.ast;

import java.util.List;

/**
 * Root AST node: the entire compilation unit.
 * Contains global declarations and function definitions in source order.
 */
public record CompUnit(List<ASTNode> items) implements ASTNode {
}
