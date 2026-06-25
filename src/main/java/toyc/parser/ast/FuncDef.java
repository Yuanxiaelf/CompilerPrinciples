package toyc.parser.ast;

import java.util.List;

/**
 * Function definition.
 * Return type is either "int" or "void".
 */
public record FuncDef(String returnType, String name, List<Param> params, Block body) implements ASTNode {
}
