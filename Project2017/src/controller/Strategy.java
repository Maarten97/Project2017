package controller;

import model.Board;
import model.Mark;

/**
 * Interface for computer strategy. Project module 2
 * 
 * @author Maarten Looijenga and Thomas Hogema
 */
public interface Strategy {

	/**
	 * Returns the name of the strategy.
	 * 
	 * @return name of the strategy
	 */
	/*@ pure */ public String getName();
	
	/**
	 * Determines a move.
	 * 
	 * @param b Board the move has to be played on.
	 * @param m Mark to be placed on the board.
	 * @return an int array with the coordinates for a move.
	 */
	public int[] determineMove(Board b, Mark m);
}
