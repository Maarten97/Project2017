package controller;

import model.Board;
import model.Mark;

/**
 * Abstract class for a player. 
 * 
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
	
 // -- Commands ---------------------------------------------------

    // @ requires board != null & !board.isFull();
    /**
     * Makes a move on the board.
     * @param board the current board
     */
    public void makeMove(Board board) {
        int[] keuze = determineMove(board);
        System.out.println("Making move: " + keuze[0] + "," + keuze[1] + "," + getMark().toString());
        board.setField(keuze[0], keuze[1], getMark());
    }
    
	/**
	 * Places a tile on the given coordinates.
	 * 
	 * @param row Row the tile has to be placed on.
	 * @param column Column the tile has to be placed on.
	 * @param m Mark to be placed on this location.
	 * @param b Board the move has to be made on
	 */
	/*
	 * @ requires name != null; requires mark == Mark.RED || mark == Mark.BLUE;
	 */
    public void placeTile(int row, int column, Mark m, Board b) {
		b.setField(row, column, m);
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
    
    /**
     * Determines the field for the next move.
     * @param board the current game board
     * @return the player's choice
     */
    /* @ requires board != null & !board.isFull();
     * @ ensures board.isField(\result) & board.isEmptyField(\result);
     */
    public abstract int[] determineMove(Board board);
}
