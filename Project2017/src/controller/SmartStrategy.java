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
	 * Returns a random free coordinate.
	 * @return a random free coordinate.
	 */
	@Override
	public int[] determineMove(Board b, Mark m) {
		// TODO to be implemented
		return CommonStrategyUtils.getRandomFreeField(b);
	}
	
	//store a point:
	//Point p = new Point (int x, int z);
	//int i = (int) p.getX();
	
	private int[] findSameColor(Board b, Mark m) {

		ArrayList<Point> sameColor = new ArrayList<Point>();
		sameColor.add(new Point(1, 2));
		for (int i = 0; i < sameColor.size(); i++) {
			// TODO test something
		}

		return null;
	}
}
