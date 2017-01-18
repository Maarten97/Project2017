package controller;

import model.*;


public class Game {
	
	private Board board;
	private Player[] players;
	private int currentPlayer;

	public Game(Player s0, Player s1) {
        board = new Board();
        players = new Player[2];
        players[0] = s0;
        players[1] = s1;
        currentPlayer = 0;
	}
	
	public Board getBoard() {
		return board;
	}
	
	/**
	 * Returns true if the game is over. The game is over when there is a winner.
	 * In this game, it is not possible to get a draw.
	 *
	 * @return true if the game is over
	 */
	// @ ensures \result == this.hasWinner();
	/* @pure */
	public boolean gameOver() {
		return this.hasWinner();
	}
	
	
	/**
	 * Checks if the mark m has won. A mark wins if it controls at least one
	 * row, column or diagonal.
	 *
	 * @param m
	 *            the mark of interest
	 * @return true if the mark has won
	 */
	public boolean isWinner(Mark m) {
		if (board.hasColumn(m)) {
			return true;
		} else if (board.hasRow(m)) {
			return true;
		} else if (board.hasPlaneDiagonal(m)) {
			return true;
		} else if (board.hasVerticalDiagonal(m)) {
			return true;
		} else if (board.hasLevel(m)) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true if the game has a winner. This is the case when one of the
	 * marks controls at least one row, column or diagonal.
	 *
	 * @return true if the student has a winner.
	 */
	// @ ensures \result == isWinner(Mark.BLUE) | \result == isWinner(Mark.RED);
	/* @pure */
	public boolean hasWinner() {
		return isWinner(Mark.BLUE) || isWinner(Mark.RED);
	}
}
