package toyc.semantic;

import java.util.HashMap;
import java.util.Map;

/**
 * Nested-scope symbol table.
 */
public class SymbolTable {

    private final SymbolTable parent;
    private final Map<String, Symbol> symbols;

    public SymbolTable() {
        this(null);
    }

    public SymbolTable(SymbolTable parent) {
        this.parent = parent;
        this.symbols = new HashMap<>();
    }

    public SymbolTable getParent() {
        return parent;
    }

    /**
     * Define a symbol in the current scope.
     * Returns false if already defined in this scope.
     */
    public boolean define(Symbol sym) {
        if (symbols.containsKey(sym.getName())) {
            return false;
        }
        symbols.put(sym.getName(), sym);
        return true;
    }

    /**
     * Look up a symbol, searching outward through parent scopes.
     * Returns null if not found.
     */
    public Symbol lookup(String name) {
        Symbol s = symbols.get(name);
        if (s != null) return s;
        if (parent != null) return parent.lookup(name);
        return null;
    }

    /**
     * Look up a symbol only in the current scope (no parent search).
     */
    public Symbol lookupLocal(String name) {
        return symbols.get(name);
    }

    /**
     * Check if a symbol is defined in the current scope.
     */
    public boolean contains(String name) {
        return symbols.containsKey(name);
    }

    public int size() {
        return symbols.size();
    }
}
