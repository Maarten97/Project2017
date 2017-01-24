package controller;

import model.Board;
import model.Mark;

public class SmartStrategy implements Strategy {

	// -- Instance variables -----------------------------------------
	private static String name = "Smart";
		
	// -- Queries ----------------------------------------------------
	/**
	 * Returns the name of this strategy.
	 * @return strategy name
	 */
	@Override
	public String getName() {
		return name;
	}

	/**
	 * Returns a random free coordinate.
	 * @return a random free coordinate.
	 */
	@Override
	public int[] determineMove(Board b, Mark m) {
		// TODO to be implemented
		return CommonStrategyUtils.getRandomFreeField(b);
	}

}
