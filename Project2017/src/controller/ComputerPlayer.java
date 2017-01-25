package controller;

import model.Board;
import model.Mark;

/**
 * Class for maintaining a computer player. Module 2 project 2017
 * 
 * @author Maarten Looijenga en Thomas Hogema
 */
public class ComputerPlayer extends Player {

	// -- Instance variables -----------------------------------------
	private Strategy strat;

	// -- Constructors -----------------------------------------------

	/*
	 * @ requires mark == Mark.XX || mark == Mark.OO; requires strategy != null;
	 * ensures this.getMark() == mark;
	 */
	/**
	 * Creates a a new Computer Player.
	 * 
	 */
	public ComputerPlayer(Mark mark, Strategy strategy) {
		super(strategy.getName() + "-" + mark.toString(), mark);
		strat = strategy;
	}

	/**
	 * Creates naive player
	 * @param mark
	 */
	public ComputerPlayer(Mark mark) {
		this(mark, new NaiveStrategy());
	}

	// -- Commands ---------------------------------------------------

	/*
	 * @ requires board != null; ensures board.isField(\result) &&
	 * board.isEmptyField(\result);
	 * 
	 */
	public int[] determineMove(Board board) {
		return strat.determineMove(board, mark);
	}

	/*
	 * @ ensures \result == strat;
	 */
	public Strategy getStrategy() {
		return strat;
	}

	/*
	 * @ ensures this.strat == strategy;
	 */
	public void setStrategy(Strategy strategy) {
		this.strat = strategy;
	}

}
