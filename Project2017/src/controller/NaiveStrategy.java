package controller;

import exception.FieldNotExsistException;
import model.Board;
import model.Mark;

public class NaiveStrategy implements Strategy {

	// -- Instance variables -----------------------------------------
	private static String name = "Naive";
	
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
	 * @throws FieldNotExsistException 
	 */
	@Override
	public int[] determineMove(Board b, Mark m) throws FieldNotExsistException {
		return CommonStrategyUtils.getRandomFreeField(b);
	}

}
