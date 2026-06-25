package toyc.parser.ast;

import java.util.List;

/**
 * Function call expression: name( arg, arg, ... )
 */
public record CallExpr(String funcName, List<Expr> args, int line) implements Expr {
}
