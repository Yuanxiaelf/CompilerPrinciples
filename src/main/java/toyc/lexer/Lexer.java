package toyc.lexer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Hand-written lexer for ToyC language.
 * Reads source code and produces a stream of tokens.
 */
public class Lexer {

    private static final Map<String, TokenType> KEYWORDS = Map.ofEntries(
            Map.entry("int", TokenType.INT),
            Map.entry("void", TokenType.VOID),
            Map.entry("const", TokenType.CONST),
            Map.entry("if", TokenType.IF),
            Map.entry("else", TokenType.ELSE),
            Map.entry("while", TokenType.WHILE),
            Map.entry("break", TokenType.BREAK),
            Map.entry("continue", TokenType.CONTINUE),
            Map.entry("return", TokenType.RETURN)
    );

    private final String source;
    private int pos;
    private int line;
    private int column;
    private final List<String> errors;

    public Lexer(String source) {
        this.source = source;
        this.pos = 0;
        this.line = 1;
        this.column = 1;
        this.errors = new ArrayList<>();
    }

    public List<String> getErrors() {
        return errors;
    }

    public boolean hasErrors() {
        return !errors.isEmpty();
    }

    /**
     * Tokenizes the entire source and returns all tokens.
     */
    public List<Token> tokenize() {
        List<Token> tokens = new ArrayList<>();
        Token token;
        do {
            token = nextToken();
            tokens.add(token);
        } while (token.type() != TokenType.EOF);
        return tokens;
    }

    /**
     * Reads and returns the next token from the source.
     */
    public Token nextToken() {
        skipWhitespaceAndComments();

        if (pos >= source.length()) {
            return makeToken(TokenType.EOF, "");
        }

        char ch = peek();

        // Identifier or keyword
        if (Character.isLetter(ch) || ch == '_') {
            return readIdentifierOrKeyword();
        }

        // Number (including negative numbers)
        if (ch == '-' && pos + 1 < source.length() && Character.isDigit(source.charAt(pos + 1))) {
            return readNumber();
        }
        if (Character.isDigit(ch)) {
            return readNumber();
        }

        // Operators and delimiters
        return readOperatorOrDelimiter();
    }

    private char peek() {
        if (pos >= source.length()) {
            return '\0';
        }
        return source.charAt(pos);
    }

    private char peekNext() {
        if (pos + 1 >= source.length()) {
            return '\0';
        }
        return source.charAt(pos + 1);
    }

    private char advance() {
        char ch = source.charAt(pos);
        pos++;
        if (ch == '\n') {
            line++;
            column = 1;
        } else {
            column++;
        }
        return ch;
    }

    private Token makeToken(TokenType type, String lexeme) {
        return new Token(type, lexeme, line, column);
    }

    private void skipWhitespaceAndComments() {
        while (pos < source.length()) {
            char ch = peek();

            // Whitespace
            if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') {
                advance();
                continue;
            }

            // Single-line comment //
            if (ch == '/' && peekNext() == '/') {
                advance(); // skip /
                advance(); // skip /
                while (pos < source.length() && peek() != '\n') {
                    advance();
                }
                continue;
            }

            // Multi-line comment /* */
            if (ch == '/' && peekNext() == '*') {
                advance(); // skip /
                advance(); // skip *
                while (pos < source.length()) {
                    if (peek() == '*' && peekNext() == '/') {
                        advance(); // skip *
                        advance(); // skip /
                        break;
                    }
                    if (pos >= source.length() - 1) {
                        errors.add(String.format("Line %d: unclosed multi-line comment", line));
                        break;
                    }
                    advance();
                }
                continue;
            }

            break;
        }
    }

    private Token readIdentifierOrKeyword() {
        int startCol = column;
        int startLine = line;
        StringBuilder sb = new StringBuilder();
        while (pos < source.length()) {
            char ch = peek();
            if (Character.isLetterOrDigit(ch) || ch == '_') {
                sb.append(advance());
            } else {
                break;
            }
        }
        String lexeme = sb.toString();
        TokenType type = KEYWORDS.getOrDefault(lexeme, TokenType.ID);
        return new Token(type, lexeme, startLine, startCol);
    }

    /**
     * Reads a NUMBER token. Per grammar: -?(0|[1-9][0-9]*)
     */
    private Token readNumber() {
        int startCol = column;
        int startLine = line;
        StringBuilder sb = new StringBuilder();

        char ch = peek();

        // Handle negative sign (only when followed by a digit)
        if (ch == '-') {
            sb.append(advance());
        }

        // Read digits
        ch = peek();
        if (ch == '0') {
            sb.append(advance());
        } else if (ch >= '1' && ch <= '9') {
            sb.append(advance());
            while (pos < source.length() && Character.isDigit(peek())) {
                sb.append(advance());
            }
        } else {
            // This shouldn't happen since we checked before calling
            errors.add(String.format("Line %d: invalid number", line));
        }

        return new Token(TokenType.NUMBER, sb.toString(), startLine, startCol);
    }

    private Token readOperatorOrDelimiter() {
        char ch = advance();

        return switch (ch) {
            case '+' -> makeToken(TokenType.PLUS, "+");
            case '-' -> makeToken(TokenType.MINUS, "-");
            case '*' -> makeToken(TokenType.STAR, "*");
            case '/' -> makeToken(TokenType.SLASH, "/");
            case '%' -> makeToken(TokenType.PERCENT, "%");
            case '(' -> makeToken(TokenType.LPAREN, "(");
            case ')' -> makeToken(TokenType.RPAREN, ")");
            case '{' -> makeToken(TokenType.LBRACE, "{");
            case '}' -> makeToken(TokenType.RBRACE, "}");
            case ';' -> makeToken(TokenType.SEMICOLON, ";");
            case ',' -> makeToken(TokenType.COMMA, ",");

            case '!' -> {
                if (peek() == '=') {
                    advance();
                    yield makeToken(TokenType.NE, "!=");
                }
                yield makeToken(TokenType.NOT, "!");
            }

            case '=' -> {
                if (peek() == '=') {
                    advance();
                    yield makeToken(TokenType.EQ, "==");
                }
                yield makeToken(TokenType.ASSIGN, "=");
            }

            case '<' -> {
                if (peek() == '=') {
                    advance();
                    yield makeToken(TokenType.LE, "<=");
                }
                yield makeToken(TokenType.LT, "<");
            }

            case '>' -> {
                if (peek() == '=') {
                    advance();
                    yield makeToken(TokenType.GE, ">=");
                }
                yield makeToken(TokenType.GT, ">");
            }

            case '&' -> {
                if (peek() == '&') {
                    advance();
                    yield makeToken(TokenType.AND, "&&");
                }
                errors.add(String.format("Line %d: unexpected '&' (did you mean '&&'?)", line));
                yield makeToken(TokenType.AND, "&");
            }

            case '|' -> {
                if (peek() == '|') {
                    advance();
                    yield makeToken(TokenType.OR, "||");
                }
                errors.add(String.format("Line %d: unexpected '|' (did you mean '||'?)", line));
                yield makeToken(TokenType.OR, "|");
            }

            default -> {
                errors.add(String.format("Line %d: unexpected character '%c'", line, ch));
                yield makeToken(TokenType.EOF, "");
            }
        };
    }
}
