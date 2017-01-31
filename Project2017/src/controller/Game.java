package controller;

//import java.util.Observable;

import model.*;
import view.GameTUI;

public class Game /* extends Observable */ {

	/*@
	 * private invariant board != null;
	 * private invariant gameTui != null;
	 * private invariant players.length == NUMBER_PLAYERS;
	 * private invariant (\forall int i; 0 <= i && i < NUMBER_PLAYERS; players[i] != null);
	 * private invariant 0 <= current  && current < NUMBER_PLAYERS;
	 */
	private Board board;
	private Player[] players;
	private int currentPlayer;
	private GameTUI gameTui;
	public static final int NUMBER_PLAYERS = 2;
	

	
	/**
	 * Creates a new Game object with two players.
	 * 
	 * @param s0 The first player.
	 * @param s1 The second player.
	 */
    /* @ requires s0 != null;
     * @ requires s1 != null;
     */
	public Game(Player s0, Player s1) {
		gameTui = new GameTUI(this);
		board = new Board();
		players = new Player[NUMBER_PLAYERS];
		players[0] = s0;
		players[1] = s1;
		currentPlayer = 0;
	}

	/**
	 * Starts the game.
	 * Asks after each ended game if the user want to continue. Continues until
	 * the user does not want to play anymore.
	 */
	public void start() {
		boolean doorgaan = true;
		String input = null;
		while (doorgaan) {
			reset();
			play();
			input = GameTUI.readString("\n> Play another time? Yes/No");
			if (input.startsWith("y") || input.startsWith("Y")) {
				doorgaan = true;
			} else {
				doorgaan = false;
				gameTui.printMessage("Thanks for playing. See you next time!");
				
			}
		}
	}
	
    /**
     * Plays the game. 
     * First the (still empty) board is shown. Then the game is played until it
     * is over. Players can make a move one after the other. After each move,
     * the changed game situation is printed. in the end, the winner will be 
     * printed. If there is a draw, this will be printed.
     */
	public void play() {
		update();
		while (!this.gameOver()) {
			players[currentPlayer].makeMove(board);
			update();
			currentPlayer = (currentPlayer + 1) % NUMBER_PLAYERS;
		}
		if (hasWinner()) {
			if (isWinner(players[0].getMark())) {
				gameTui.printResult(players[0]);
			} else {
				gameTui.printResult(players[1]);
			}
		} else {
			GameTUI.printDraw();
		}
	}

	/**
	 * Resets the game. <br>
	 * The board is emptied and player[0] becomes the current player.
	 */
	public void reset() {
		currentPlayer = 0;
		board.reset();

	}

	/**
	 * Prints the game situation.
	 */
	public void update() {
		System.out.println("\ncurrent game situation: \n\n" + gameTui.printBoard() + "\n");
	}

	public Board getBoard() {
		return board;
	}

	/**
	 * Returns true if the game is over. The game is over when there is a
	 * winner. In this game, it is not possible to get a draw.
	 *
	 * @return true if the game is over
	 */
	// @ ensures \result == this.hasWinner();
	/* @pure */
	public boolean gameOver() {
		return this.hasWinner() || this.isDraw();
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
		} else if (board.hasLevel(m)) {
			return true;
		} else if (board.hasPlaneDiagonal(m)) {
			return true;
		} else if (board.hasVerticalDiagonal(m)) {
			return true;
		} else if (board.hasLevelDiagonal(m)) {
			return true;
		} else {
			return false;
		}
	}
	/**
	 * If the game has ended and there is a winner, it will return the Mark of the winner.
	 * @return Mark.BLUE or Mark.RED.
	 */
	//@ requires hasWinner() == true;
	//@ ensures \result == Mark.BLUE || \result == Mark.RED;
	public Mark getWinner() {
		if (hasWinner()) {
			if (isWinner(Mark.BLUE)) {
				return Mark.BLUE;
			} else {
				return Mark.RED;
			}
		}
		return Mark.EMPTY;
	}

	/**
	 * Get a boolean
	 *
	 * @return true if all fields are occupied
	 */
	// @ ensures \result == (\forall int i; i <= 0 & i < DIM * DIM;
	// this.getField(i) != Mark.EMPTY);
	// @ ensures hasWinner() == false
	/* @pure */
	public boolean isDraw() {
		return board.isFull();
	}
	
	public Player getCurrentPlayer(int currentPlayer){
		return players[currentPlayer];
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
