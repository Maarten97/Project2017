package model;
public enum Mark {
    
    EMPTY, RED, BLUE;

    /*@
       ensures this == Mark.RED ==> \result == Mark.RED;
       ensures this == Mark.BLUE ==> \result == Mark.BLUE;
       ensures this == Mark.EMPTY ==> \result == Mark.EMPTY;
     */
    /**
     * Returns the other mark.
     * 
     * @return The other mark. If the Mark is Empty, Empty will be returned.
     */
    public Mark other() {
        if (this == RED) {
            return BLUE;
        } else if (this == BLUE) {
            return RED;
        } else {
            return EMPTY;
        }
    }
}