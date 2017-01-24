package controller;

import model.Board;
import model.Mark;
import ss.week5.tictactoe.CommonStrategyUtils;

public class NaiveStrategy implements Strategy {

	// -- Instance variables -----------------------------------------
	private static String name = "Naive";
	
	
	public NaiveStrategy()  {
		// TODO Auto-generated constructor stub
	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
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
