package toyc.lexer;

/**
 * Token types for ToyC language.
 */
public enum TokenType {
    // Keywords
    INT("int"),
    VOID("void"),
    CONST("const"),
    IF("if"),
    ELSE("else"),
    WHILE("while"),
    BREAK("break"),
    CONTINUE("continue"),
    RETURN("return"),

    // Operators
    PLUS("+"),
    MINUS("-"),
    STAR("*"),
    SLASH("/"),
    PERCENT("%"),
    EQ("=="),
    NE("!="),
    LT("<"),
    GT(">"),
    LE("<="),
    GE(">="),
    AND("&&"),
    OR("||"),
    NOT("!"),
    ASSIGN("="),

    // Delimiters
    LPAREN("("),
    RPAREN(")"),
    LBRACE("{"),
    RBRACE("}"),
    SEMICOLON(";"),
    COMMA(","),

    // Literals and identifiers
    ID("<id>"),
    NUMBER("<number>"),

    // End of file
    EOF("<eof>");

    private final String display;

    TokenType(String display) {
        this.display = display;
    }

    public String getDisplay() {
        return display;
    }

    @Override
    public String toString() {
        return display;
    }
}
