package controller;

import model.Board;
import model.Mark;

public class ServerPlayer extends Player {

	//create a player with a name and mark
	public ServerPlayer(String name, Mark mark) {
		super(name, mark);
	}

	/**
	 * Places a tile on the given coordiantes.
	 * 
	 * @param row Row the tile has to be placed on.
	 * @param column Column the tile has to be placed on.
	 * @param m Mark to be placed on this location.
	 * @param b Board the move has to be made on
	 */
	/*
	 * @ ensures 
	 */
	public void placeTile(int row, int column, int level, Mark m, Board b) {
		b.setField(row, column, m);
	}

	//moet importeren
	@Override
	public int[] determineMove(Board board) {
		return null;
	}

}
