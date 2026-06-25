package toyc.semantic;

import java.util.List;

/**
 * Symbol table entry.
 */
public class Symbol {
    public enum Kind {
        VAR,        // int variable
        CONST,      // const int
        PARAM,      // function parameter
        FUNC        // function
    }

    private final String name;
    private final Kind kind;
    private final Type type;           // INT or VOID (VOID only for functions)

    // For constants: the compile-time evaluated value
    private Integer constValue;

    // For variables/params: stack offset (assigned during codegen)
    private int offset = -1;

    // For functions
    private final String funcReturnType; // "int" or "void"
    private final List<String> funcParamNames;

    // Global flag
    private final boolean isGlobal;

    public Symbol(String name, Kind kind, Type type, boolean isGlobal) {
        this.name = name;
        this.kind = kind;
        this.type = type;
        this.isGlobal = isGlobal;
        this.funcReturnType = null;
        this.funcParamNames = null;
    }

    public Symbol(String name, String returnType, List<String> paramNames, boolean isGlobal) {
        this.name = name;
        this.kind = Kind.FUNC;
        this.type = returnType.equals("int") ? Type.INT : Type.VOID;
        this.isGlobal = isGlobal;
        this.funcReturnType = returnType;
        this.funcParamNames = paramNames;
    }

    public String getName() { return name; }
    public Kind getKind() { return kind; }
    public Type getType() { return type; }
    public boolean isGlobal() { return isGlobal; }

    public Integer getConstValue() { return constValue; }
    public void setConstValue(Integer constValue) { this.constValue = constValue; }

    public int getOffset() { return offset; }
    public void setOffset(int offset) { this.offset = offset; }

    public String getFuncReturnType() { return funcReturnType; }
    public List<String> getFuncParamNames() { return funcParamNames; }

    public boolean isConst() { return kind == Kind.CONST; }
    public boolean isFunc() { return kind == Kind.FUNC; }

    @Override
    public String toString() {
        return String.format("Symbol{%s %s %s}", kind, type, name);
    }
}
