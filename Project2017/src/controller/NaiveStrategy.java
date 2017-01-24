package controller;

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
	 * Returns a random free index, and -1 if the bord is full.
	 * @return a random free index; -1 if there are no free indexes.
	 */
	//gets the available empty fields from the game.
	@Override
	public int determineMove(Board b, Mark m) {
		return CommonStrategyUtils.getRandomFreeField(b);
	}

}
