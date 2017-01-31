package controller;

import model.Board;
import model.Mark;

/**
 * Class for maintaining a computer player.
 * 
 * @author Maarten Looijenga en Thomas Hogema
 */
public class ComputerPlayer extends Player {

	// -- Instance variables -----------------------------------------
	
	private Strategy strat;

	// -- Constructors -----------------------------------------------

	/**
	 * Creates a a new Computer Player with a name and strategy.
	 * 
	 * @param mark the mark of the computer player you want to create.
	 * @param strategy the strategy of the computer player you want to create.
	 */
	/*  @ requires mark == Mark.XX || mark == Mark.OO; requires strategy != null;
	 *  @ ensures this.getMark() == mark; 
	 */
	public ComputerPlayer(Mark mark, Strategy strategy) {
		super(strategy.getName() + "-" + mark.toString(), mark);
		strat = strategy;
	}
	
	/**
	 * Creates a computerPlayer with an custom name. This constructor is used by the clients
	 * and the servers. The default strategy is SmartStrategy
	 * 
	 * @param name Name of the created ComputerPlayer
	 * @param mark Mark of the created ComputerPlayer
	 */
	/*  @ requires mark == Mark.XX || mark == Mark.OO; requires name != null;
	 *  @ ensures this.getMark() == mark; 
	 */
	public ComputerPlayer(String name, Mark mark) {
		super(name, mark);
		strat = new SmartStrategy();
	}

	/**
	 * Creates a naive ComputerPlayer.
	 * 
	 * @param mark the mark to the ComputerPlayer you want to create.
	 */
	/*  @ requires mark == Mark.XX || mark == Mark.OO;
	 *  @ ensures this.getMark() == mark; 
	 */
	public ComputerPlayer(Mark mark) {
		this(mark, new NaiveStrategy());
	}

	// -- Commands ---------------------------------------------------

	/**
	 * Determines move according to strategy.
	 * 
	 * @return the determined move as int array.
	 */
	/* @ requires board != null; ensures board.isField(\result) &&
	 * @ board.isEmptyField(\result);
	 */
	public int[] determineMove(Board board) {
		return strat.determineMove(board, mark);
	}
	
	/**
	 * Sets the strategy of this ComputerPlayer.
	 * 
	 * @param strategy the strategy you want to set.
	 */
	/*  @ requires strategy != null;
	 *  @ ensures this.strat == strategy;
	 */
	public void setStrategy(Strategy strategy) {
		this.strat = strategy;
	}
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns the strategy of this ComputerPlayer.
	 * 
	 * @return strategy of this ComputerPlayer.
	 */
	// @ ensures \result == strat;
	public Strategy getStrategy() {
		return strat;
	}
}
