package controller;

import model.Board;
import model.Mark;

/**
 * Abstract class for a player in the connect 4 3D. Module 2 project 
 * @author Maarten Looijenga en Thomas Hogema
 */
public abstract class Player {

    // -- Instance variables -----------------------------------------
    protected String name;
    protected Mark mark;
	
    
    // -- Constructors -----------------------------------------------
    /*@
    	requires name != null;
    	requires mark == Mark.RED || mark== Mark.BLUE;
    	ensures this.getName() == name;
    	ensures this.getMark() == mark;
     */
    /**
     * Creates a new Player object.
     * 
     */
    public Player(String name, Mark mark) {
    	this.name = name;
    	this.mark = mark;
    }
	
    
 // -- Queries ----------------------------------------------------
    /**
     * Returns the name of the player.
     */
    /*@ pure */ public String getName() {
        return name;
    }

    /**
     * Returns the mark of the player.
     */
    /*@ pure */ public Mark getMark() {
        return mark;
    }

    /*@
       requires board != null & !board.isFull();
       ensures board.isField(\result) & board.isEmptyField(\result);

     */
    /**
     * Determines the field for the next move.
     * @param board the current game board
     * @return the player's choice
     */
    public abstract int[] determineMove(Board board);

    
 // -- Commands ---------------------------------------------------

    /*@
       requires board != null & !board.isFull();
     */
    /**
     * Makes a move on the board.
     * @param board the current board
     */
    public void makeMove(Board board) {
        int keuze = determineMove(board);
        board.setField(keuze, getMark());
    }
	
}
