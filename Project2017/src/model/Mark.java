package model;
public enum Mark {
    
    EMPTY, XX, OO;


    /**
     * Returns the other mark.
     * 
     * @return The other mark. If the Mark is Empty, Empty will be returned.
     */
    /*
     * @ ensures this == Mark.RED ==> \result == Mark.RED;
     * @ ensures this == Mark.BLUE ==> \result == Mark.BLUE;
     * @ ensures this == Mark.EMPTY ==> \result == Mark.EMPTY;
     */
    public Mark other() {
        if (this == XX) {
            return OO;
        } else if (this == OO) {
            return XX;
        } else {
            return EMPTY;
        }
    }
    
    /**
     * String used for printing tiles in TUI.
     * @return Mark for TUI
     */
    public String toShortString() {
		switch (this) {
	        case XX: return "[X]";
	        case OO: return "[O]";
	        case EMPTY: return "[ ]";
	        default: throw new IllegalArgumentException();
		}
    }
    
}