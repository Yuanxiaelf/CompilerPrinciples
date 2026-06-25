package toyc.semantic;

/**
 * Types in ToyC language.
 */
public enum Type {
    INT,
    VOID;

    @Override
    public String toString() {
        return name().toLowerCase();
    }
}
