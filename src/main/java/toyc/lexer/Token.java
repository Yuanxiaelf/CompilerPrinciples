package toyc.lexer;

/**
 * Represents a lexical token in ToyC source code.
 */
public record Token(TokenType type, String lexeme, int line, int column) {

    @Override
    public String toString() {
        return String.format("Token{%s '%s' at %d:%d}", type, lexeme, line, column);
    }
}
