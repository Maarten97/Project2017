package controller;

import model.Board;
import model.Mark;
import java.awt.Point;
import java.util.*;

public class SmartStrategy implements Strategy {

	// -- Instance variables -----------------------------------------
	private static String name = "Smart";
		
	// -- Queries ----------------------------------------------------
	/**
	 * Returns the name of this strategy.
	 * @return strategy name
	 */
	@Override
	/*@ pure */ public String getName() {
		return name;
	}

	/**
	 * Returns to some extend smart move.
	 * 
	 * @return next move as int array
	 */
	// @ assures /result != null;
	@Override
	public int[] determineMove(Board b, Mark m) {
		//checks if there is a move that will win the game
		if (moveToWin(b, m) != null) {
			return moveToWin(b, m);
		}
		
		//checks if there is a move that blocks the opponent winning a game
		if (moveToWin(b, m.other()) != null) {
			return moveToWin(b, m.other());
		}
		
		//builds a column
		if (possibleColumn(b, m) != null) {
			return possibleColumn(b, m);
		}
		
		//if all else fails; make a random move
		return CommonStrategyUtils.getRandomFreeField(b);
	}
	
	//store a point:
	//Point p = new Point (int x, int z);
	//int i = (int) p.getX();
	
//	private int[] findSameColor(Board b, Mark m) {
//		ArrayList<Point> sameColor = new ArrayList<Point>();
//		sameColor.add(new Point(1, 2));
//		for (int i = 0; i < sameColor.size(); i++) {
//			// TODO test something
//		}
//
//		return null;
//	}
	
	/**
	 * Very basic strategy which tries to build columns.
	 * 
	 * @param b Board to play on
	 * @param m Mark to be placed
	 * @return next move as int array
	 */
	private int[] possibleColumn(Board b, Mark m) {
		for (int col = 0; col < Board.DIM; col++) {
			for (int row = 0; row < Board.DIM; row++) {
				boolean sameOrEmpty = true;
				for (int level = 0; level < Board.DIM; level++) {
					if (b.getField(row, col, level) == m.other()) {
						sameOrEmpty = false;
					}
				}
				System.out.println("Looked at: " + row+","+col+" sameOrEmpty: " + sameOrEmpty);
				if (sameOrEmpty == true) {
					return new int[]{row, col};
				}
			}
		}
		//this should only happen if every possible column contains a tile from the opponent.
		return null;
	}
	
	/**
	 * Returns a winning move, if present.
	 * 
	 * @param board The board to play on
	 * @param m The mark to be played
	 * @return the winning move as int array
	 */
	private int[] moveToWin(Board board, Mark m) {
		for (int row = 0; row < Board.DIM; row++) {
			for (int col = 0; col < Board.DIM; col++) {
				Board b = board.deepCopy();
				if (b.validMove(row, col)) {
					b.setField(row, col, m);
					if (b.isWinner(m)) {
						return new int[]{row, col};
					}
				}
			}
		}
		return null;
	}
}
