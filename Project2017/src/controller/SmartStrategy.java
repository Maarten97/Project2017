package controller;

import model.Board;
import model.Mark;

public class SmartStrategy implements Strategy {

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

	@Override
	public int determineMove(Board b, Mark m) {
		// TODO Auto-generated method stub
		return 0;
	}

}
