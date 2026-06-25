package toyc.parser;

import toyc.lexer.Token;
import toyc.lexer.TokenType;
import toyc.parser.ast.*;

import java.util.ArrayList;
import java.util.List;

/**
 * Recursive-descent parser with operator precedence climbing for expressions.
 */
public class Parser {

    private final List<Token> tokens;
    private int pos;
    private final List<String> errors;

    // Precedence levels (higher = tighter binding)
    private static final int PREC_NONE = 0;
    private static final int PREC_OR = 1;       // ||
    private static final int PREC_AND = 2;      // &&
    private static final int PREC_REL = 3;      // == != < > <= >=
    private static final int PREC_ADD = 4;      // + -
    private static final int PREC_MUL = 5;      // * / %

    public Parser(List<Token> tokens) {
        this.tokens = tokens;
        this.pos = 0;
        this.errors = new ArrayList<>();
    }

    public List<String> getErrors() {
        return errors;
    }

    public boolean hasErrors() {
        return !errors.isEmpty();
    }

    // ========== Parse entry ==========

    public CompUnit parseCompUnit() {
        List<ASTNode> items = new ArrayList<>();
        while (!isEOF()) {
            items.add(parseTopLevelItem());
        }
        return new CompUnit(items);
    }

    // ========== Top-level items ==========

    /**
     * Top-level: Decl (VarDecl/ConstDecl) or FuncDef.
     */
    private ASTNode parseTopLevelItem() {
        if (match(TokenType.CONST)) {
            return parseConstDecl();
        }
        if (match(TokenType.INT)) {
            // Look ahead: int ID = ... → VarDecl, int ID ( ... → FuncDef
            if (peekIs(TokenType.ID) && peekNextIs(TokenType.LPAREN)) {
                return parseFuncDef("int");
            }
            // Must be VarDecl or global variable
            // Need to re-parse the "int" prefix
            // We already consumed "int", so we need to parse the rest
            return parseVarDeclAfterInt();
        }
        if (match(TokenType.VOID)) {
            return parseFuncDef("void");
        }
        error("expected declaration or function definition");
        skipToSync();
        return null;
    }

    /**
     * Parse VarDecl after "int" has already been consumed.
     */
    private VarDecl parseVarDeclAfterInt() {
        Token id = expect(TokenType.ID);
        expect(TokenType.ASSIGN);
        Expr init = parseExpr();
        expect(TokenType.SEMICOLON);
        return new VarDecl(id.lexeme(), init, id.line());
    }

    /**
     * Parse ConstDecl: "const" already consumed.
     */
    private ConstDecl parseConstDecl() {
        expect(TokenType.INT);
        Token id = expect(TokenType.ID);
        expect(TokenType.ASSIGN);
        Expr init = parseExpr();
        expect(TokenType.SEMICOLON);
        return new ConstDecl(id.lexeme(), init, id.line());
    }

    /**
     * Parse FuncDef. The return type token ("int" or "void") has been consumed.
     * Called with returnType = "int" when "int" was already consumed.
     */
    private FuncDef parseFuncDef(String returnType) {
        Token id = expect(TokenType.ID);
        expect(TokenType.LPAREN);
        List<Param> params = new ArrayList<>();
        if (!check(TokenType.RPAREN)) {
            params.add(parseParam());
            while (match(TokenType.COMMA)) {
                params.add(parseParam());
            }
        }
        expect(TokenType.RPAREN);
        Block body = parseBlock();
        return new FuncDef(returnType, id.lexeme(), params, body);
    }

    private Param parseParam() {
        expect(TokenType.INT);
        Token id = expect(TokenType.ID);
        return new Param(id.lexeme());
    }

    // ========== Declarations (inside blocks) ==========

    /**
     * Parse a declaration (VarDecl or ConstDecl).
     * Called when inside a function body (not at top level).
     */
    private Decl parseDecl() {
        if (match(TokenType.CONST)) {
            return parseConstDecl();
        }
        if (match(TokenType.INT)) {
            return parseVarDeclAfterInt();
        }
        error("expected 'int' or 'const' for declaration");
        skipToSync();
        return null;
    }

    // ========== Statements ==========

    private Stmt parseStmt() {
        // Block
        if (check(TokenType.LBRACE)) {
            return parseBlock();
        }

        // Empty statement
        if (match(TokenType.SEMICOLON)) {
            return new NullStmt();
        }

        // Declarations
        if (check(TokenType.CONST)) {
            return parseDecl();
        }
        if (check(TokenType.INT)) {
            // Inside function body, "int" always starts VarDecl
            // (no nested function definitions)
            advance(); // consume "int"
            return parseVarDeclAfterInt();
        }

        // Control flow
        if (match(TokenType.IF)) {
            return parseIfStmt();
        }
        if (match(TokenType.WHILE)) {
            return parseWhileStmt();
        }
        if (match(TokenType.BREAK)) {
            Token t = prevToken();
            expect(TokenType.SEMICOLON);
            return new BreakStmt(t.line());
        }
        if (match(TokenType.CONTINUE)) {
            Token t = prevToken();
            expect(TokenType.SEMICOLON);
            return new ContinueStmt(t.line());
        }
        if (match(TokenType.RETURN)) {
            return parseReturnStmt();
        }

        // Assignment or expression statement
        // ID = ... → AssignStmt
        // ID ( ... → ExprStmt (function call)
        // other expr → ExprStmt
        if (check(TokenType.ID) && peekNextIs(TokenType.ASSIGN)) {
            Token id = advance(); // consume ID
            advance(); // consume =
            Expr value = parseExpr();
            expect(TokenType.SEMICOLON);
            return new AssignStmt(id.lexeme(), value, id.line());
        }

        // Expression statement
        Expr expr = parseExpr();
        expect(TokenType.SEMICOLON);
        return new ExprStmt(expr);
    }

    private Block parseBlock() {
        expect(TokenType.LBRACE);
        List<Stmt> stmts = new ArrayList<>();
        while (!check(TokenType.RBRACE) && !isEOF()) {
            stmts.add(parseStmt());
        }
        expect(TokenType.RBRACE);
        return new Block(stmts);
    }

    private IfStmt parseIfStmt() {
        expect(TokenType.LPAREN);
        Expr condition = parseExpr();
        expect(TokenType.RPAREN);
        Stmt thenStmt = parseStmt();
        Stmt elseStmt = null;
        if (match(TokenType.ELSE)) {
            elseStmt = parseStmt();
        }
        return new IfStmt(condition, thenStmt, elseStmt);
    }

    private WhileStmt parseWhileStmt() {
        expect(TokenType.LPAREN);
        Expr condition = parseExpr();
        expect(TokenType.RPAREN);
        Stmt body = parseStmt();
        return new WhileStmt(condition, body);
    }

    private ReturnStmt parseReturnStmt() {
        int line = prevToken().line();
        if (check(TokenType.SEMICOLON)) {
            advance(); // consume ;
            return new ReturnStmt(null, line);
        }
        Expr value = parseExpr();
        expect(TokenType.SEMICOLON);
        return new ReturnStmt(value, line);
    }

    // ========== Expressions (Precedence Climbing) ==========

    public Expr parseExpr() {
        return parseExpr(PREC_NONE);
    }

    /**
     * Precedence climbing expression parser.
     */
    private Expr parseExpr(int minPrec) {
        Expr left = parseUnary();

        while (true) {
            Token op = peek();
            int prec = getPrecedence(op);
            if (prec <= minPrec) break;

            advance(); // consume operator
            Expr right = parseExpr(prec);
            left = new BinaryExpr(left, op.lexeme(), right, op.line());
        }

        return left;
    }

    private Expr parseUnary() {
        Token t = peek();
        if (t.type() == TokenType.PLUS || t.type() == TokenType.MINUS || t.type() == TokenType.NOT) {
            advance();
            Expr operand = parseUnary();
            return new UnaryExpr(t.lexeme(), operand, t.line());
        }
        return parsePrimary();
    }

    private Expr parsePrimary() {
        // NUMBER
        if (match(TokenType.NUMBER)) {
            Token t = prevToken();
            return new LiteralExpr(Integer.parseInt(t.lexeme()), t.line());
        }

        // LPAREN Expr RPAREN
        if (match(TokenType.LPAREN)) {
            Expr expr = parseExpr();
            expect(TokenType.RPAREN);
            return expr;
        }

        // ID [ ( args ) ]
        if (check(TokenType.ID)) {
            Token id = advance();
            if (match(TokenType.LPAREN)) {
                // Function call
                List<Expr> args = new ArrayList<>();
                if (!check(TokenType.RPAREN)) {
                    args.add(parseExpr());
                    while (match(TokenType.COMMA)) {
                        args.add(parseExpr());
                    }
                }
                expect(TokenType.RPAREN);
                return new CallExpr(id.lexeme(), args, id.line());
            }
            return new IdExpr(id.lexeme(), id.line());
        }

        error("expected expression, got " + peek());
        skipToSync();
        return new LiteralExpr(0, peek().line());
    }

    // ========== Operator precedence ==========

    private int getPrecedence(Token op) {
        return switch (op.type()) {
            case OR -> PREC_OR;
            case AND -> PREC_AND;
            case EQ, NE, LT, GT, LE, GE -> PREC_REL;
            case PLUS, MINUS -> PREC_ADD;
            case STAR, SLASH, PERCENT -> PREC_MUL;
            default -> PREC_NONE;
        };
    }

    // ========== Token helpers ==========

    private Token peek() {
        if (pos < tokens.size()) {
            return tokens.get(pos);
        }
        return new Token(TokenType.EOF, "", -1, -1);
    }

    private Token advance() {
        Token t = peek();
        if (pos < tokens.size()) {
            pos++;
        }
        return t;
    }

    private Token prevToken() {
        if (pos > 0 && pos <= tokens.size()) {
            return tokens.get(pos - 1);
        }
        return new Token(TokenType.EOF, "", -1, -1);
    }

    private boolean check(TokenType type) {
        return peek().type() == type;
    }

    private boolean match(TokenType type) {
        if (check(type)) {
            advance();
            return true;
        }
        return false;
    }

    private boolean peekIs(TokenType type) {
        return peek().type() == type;
    }

    private boolean peekNextIs(TokenType type) {
        if (pos + 1 < tokens.size()) {
            return tokens.get(pos + 1).type() == type;
        }
        return false;
    }

    private Token expect(TokenType type) {
        Token t = advance();
        if (t.type() != type) {
            error(String.format("expected %s but got %s '%s' at line %d",
                    type, t.type(), t.lexeme(), t.line()));
        }
        return t;
    }

    private boolean isEOF() {
        return peek().type() == TokenType.EOF;
    }

    // ========== Error handling ==========

    private void error(String msg) {
        errors.add(String.format("Line %d: %s", peek().line(), msg));
    }

    /**
     * Panic-mode error recovery: skip tokens until a synchronization point.
     */
    private void skipToSync() {
        while (!isEOF()) {
            Token t = peek();
            // Synchronize at statement boundaries
            if (t.type() == TokenType.SEMICOLON ||
                    t.type() == TokenType.RBRACE ||
                    t.type() == TokenType.LBRACE) {
                if (t.type() == TokenType.SEMICOLON) {
                    advance();
                }
                return;
            }
            // Synchronize at keywords that start new declarations/statements
            if (t.type() == TokenType.INT || t.type() == TokenType.VOID ||
                    t.type() == TokenType.CONST || t.type() == TokenType.IF ||
                    t.type() == TokenType.WHILE || t.type() == TokenType.RETURN ||
                    t.type() == TokenType.BREAK || t.type() == TokenType.CONTINUE) {
                return;
            }
            advance();
        }
    }
}
