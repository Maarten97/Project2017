package controller;

import model.Board;
import model.Mark;

/**
 * Class for a server player. This player runs on the server to fulfill the role of opponent.
 * 
 * @author Maarten Looijenga en Thomas Hogema
 */
public class ServerPlayer extends Player {

	// -- Constructors -----------------------------------------------

	/**
	 * Create a player with a name and mark.
	 * 
	 * @param name Name to give the ServerPlayer
	 * @param mark Mark to give the ServerPlayer
	 */
	/*
	 * @ requires name != null; requires mark == Mark.RED || mark == Mark.BLUE;
	 * @ ensures this.getName() == name; ensures this.getMark() == mark;
	 */
	public ServerPlayer(String name, Mark mark) {
		super(name, mark);
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

	/**
	 * Needs to be overwritten because Player is an abstract class.
	 * Redundant code.
	 */
	@Override
	public int[] determineMove(Board board) {
		return null;
	}

}
