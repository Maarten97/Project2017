package controller;

import model.Board;
import model.Mark;

public class ServerPlayer extends Player {

	//create a player with a name and mark
	public ServerPlayer(String name, Mark mark) {
		super(name, mark);
	}

	//plaatst een tile op de gegeven coordinaten.
	public boolean placeTile(int row, int column, int level, Mark m, Board b) {
		if (b.validMove(column,  row)) {
			return true;
		}
		return false;
	}

	//moet importeren
	@Override
	public int[] determineMove(Board board) {
		return null;
	}

}
