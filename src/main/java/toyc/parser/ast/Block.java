package toyc.parser.ast;

import java.util.List;

/**
 * Block statement: { stmt* }
 */
public record Block(List<Stmt> stmts) implements Stmt {
}
