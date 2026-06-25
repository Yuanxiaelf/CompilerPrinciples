package toyc;

import toyc.lexer.Lexer;
import toyc.lexer.Token;
import toyc.parser.Parser;
import toyc.parser.ast.CompUnit;
import toyc.codegen.CodeGenerator;
import toyc.semantic.SemanticAnalyzer;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.List;

/**
 * Entry point for the ToyC compiler.
 * Reads ToyC source from stdin, outputs RISC-V32 assembly to stdout.
 */
public class Main {

    public static void main(String[] args) {
        boolean optimize = false;
        for (String arg : args) {
            if ("-opt".equals(arg)) {
                optimize = true;
            }
        }

        // Read source from stdin
        String source;
        try {
            byte[] bytes = System.in.readAllBytes();
            source = new String(bytes, StandardCharsets.UTF_8);
        } catch (IOException e) {
            System.err.println("Error reading stdin: " + e.getMessage());
            System.exit(1);
            return;
        }

        // Phase 1: Lexical analysis
        Lexer lexer = new Lexer(source);
        List<Token> tokens = lexer.tokenize();

        if (lexer.hasErrors()) {
            for (String err : lexer.getErrors()) {
                System.err.println("Lexer error: " + err);
            }
            System.exit(1);
            return;
        }

        // Phase 2-3: Parse tokens into AST
        Parser parser = new Parser(tokens);
        CompUnit ast = parser.parseCompUnit();

        if (parser.hasErrors()) {
            for (String err : parser.getErrors()) {
                System.err.println("Parse error: " + err);
            }
            System.exit(1);
            return;
        }

        // Phase 4: Semantic analysis
        SemanticAnalyzer analyzer = new SemanticAnalyzer();
        analyzer.analyze(ast);

        if (analyzer.hasErrors()) {
            for (String err : analyzer.getErrors()) {
                System.err.println("Semantic error: " + err);
            }
            System.exit(1);
            return;
        }

        // Phase 5-7: Code generation
        CodeGenerator codegen = new CodeGenerator(analyzer);
        String assembly = codegen.generate(ast);

        // Output assembly to stdout
        System.out.print(assembly);
    }
}
