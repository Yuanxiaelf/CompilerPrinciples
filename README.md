# ToyC Compiler

A ToyC → RISC-V32 compiler built in Java 21, featuring hand-written lexer, recursive descent parser with precedence climbing, nested-scope semantic analysis, and RV32IM code generation. Zero external dependencies.

## Features

### Language Support (ToyC — a C subset)

| Category | Supported |
|----------|-----------|
| Types | `int`, `void`, `const int` |
| Expressions | Arithmetic (`+ - * / %`), Relational (`< > <= >= == !=`), Logical (`&& \|\| !`) |
| Short-circuit | `&&` and `\|\|` evaluate right operand only when necessary |
| Statements | Assignment, `if`-`else`, `while`, `break`, `continue`, `return`, blocks |
| Functions | Multiple `int` parameters, recursion, nested calls, `void` functions |
| Scoping | Nested block scopes with name shadowing |
| Globals | Global variables and constants with `.data` section |
| Constants | Compile-time constant folding for `const int` declarations |

### Semantic Checks
- Undefined identifier detection
- Constant reassignment prevention
- `break`/`continue` placement validation
- `main` function existence and signature
- Return path completeness for `int` functions
- Argument count matching
- Division by zero (literal divisors)

### Code Generation
- Target: **RISC-V32 (RV32IM)** — integer base + multiply/divide
- Stack frames with frame pointer (`s0`)
- Register-based expression evaluation (`t0`–`t6`)
- Short-circuit evaluation via conditional branches
- Recursive function support with proper call/return

## Project Structure

```
toyc/
├── pom.xml
├── README.md
└── src/main/java/toyc/
    ├── Main.java                          # Entry point, drives compilation pipeline
    ├── lexer/
    │   ├── TokenType.java                 # 20 token types
    │   ├── Token.java                     # Token record (type, lexeme, line, col)
    │   └── Lexer.java                     # Hand-written DFA lexer
    ├── parser/
    │   ├── Parser.java                    # Recursive descent + precedence climbing
    │   └── ast/                           # AST nodes (sealed interfaces + records)
    │       ├── CompUnit.java              # Root: compilation unit
    │       ├── FuncDef.java, Param.java   # Function definitions
    │       ├── VarDecl.java, ConstDecl.java  # Declarations
    │       ├── Block.java, IfStmt.java, WhileStmt.java
    │       ├── BreakStmt.java, ContinueStmt.java, ReturnStmt.java
    │       ├── AssignStmt.java, ExprStmt.java, NullStmt.java
    │       └── BinaryExpr.java, UnaryExpr.java, LiteralExpr.java,
    │           IdExpr.java, CallExpr.java
    ├── semantic/
    │   ├── Type.java                      # INT / VOID
    │   ├── Symbol.java                    # Symbol table entry
    │   ├── SymbolTable.java               # Nested-scope symbol table
    │   └── SemanticAnalyzer.java          # Type checking, const folding, resolution
    └── codegen/
        └── CodeGenerator.java             # AST → RISC-V32 assembly
```

## Build

**Requirements:** JDK 21, Maven 3.9+

```bash
mvn clean package
```

Produces `target/toyc-1.0.0.jar`.

## Usage

```bash
# Compile ToyC source to RISC-V32 assembly
java -jar target/toyc-1.0.0.jar < input.tc > output.s

# With optimization flag (currently accepted but ignored)
java -jar target/toyc-1.0.0.jar -opt < input.tc > output.s
```

## Example

**Input** (`test.tc`):
```c
int factorial(int n) {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

int main() {
    return factorial(5);  // 120
}
```

**Output** (`test.s` — RISC-V32 assembly):
```asm
.text
.globl main

factorial:
  addi sp, sp, -16
  sw   ra, 12(sp)
  sw   s0, 8(sp)
  addi s0, sp, 16
  sw   a0, -12(s0)          # store parameter n
  lw   t0, -12(s0)
  ...
  mv   a0, t0               # return value in a0
  j    .L.epilogue.factorial
.L.epilogue.factorial:
  lw   ra, 12(sp)
  lw   s0, 8(sp)
  addi sp, sp, 16
  ret

main:
  ...
  li   a0, 5
  call factorial
  ...
```

## Compilation Pipeline

```
Source (stdin)
  → Lexer        char stream → token stream
  → Parser       token stream → AST
  → SemanticAnalyzer  AST → annotated AST + error checks
  → CodeGenerator     annotated AST → RISC-V32 assembly
  → Assembly (stdout)
```

## Grammar

Full ToyC grammar as defined in the course specification:

```
CompUnit      → (Decl | FuncDef)+
Decl          → ConstDecl | VarDecl
ConstDecl     → "const" "int" ID "=" Expr ";"
VarDecl       → "int" ID "=" Expr ";"
FuncDef       → ("int" | "void") ID "(" (Param ("," Param)*)? ")" Block
Param         → "int" ID
Stmt          → Block | ";" | Expr ";" | ID "=" Expr ";" | Decl
              | "if" "(" Expr ")" Stmt ("else" Stmt)?
              | "while" "(" Expr ")" Stmt
              | "break" ";" | "continue" ";" | "return" Expr? ";"
Block         → "{" Stmt* "}"
Expr          → LOrExpr
LOrExpr       → LAndExpr | LOrExpr "||" LAndExpr
LAndExpr      → RelExpr | LAndExpr "&&" RelExpr
RelExpr       → AddExpr | RelExpr ("<"|">"|"<="|">="|"=="|"!=") AddExpr
AddExpr       → MulExpr | AddExpr ("+"|"-") MulExpr
MulExpr       → UnaryExpr | MulExpr ("*"|"/"|"%") UnaryExpr
UnaryExpr     → PrimaryExpr | ("+"|"-"|"!") UnaryExpr
PrimaryExpr   → ID | NUMBER | "(" Expr ")" | ID "(" (Expr ("," Expr)*)? ")"
```

## Design Decisions

- **No ANTLR / Flex / Bison** — Hand-written lexer and parser for zero dependencies and full control
- **No IR layer** — Direct AST → assembly generation (IR can be added later for optimizations)
- **Sealed interfaces + records** — Modern Java for clean, type-safe AST definitions
- **Simple register allocation** — `t0`–`t6` with stack push/pop for save/restore across nested expressions
- **Maven build** — Minimal configuration, standard Java project layout
