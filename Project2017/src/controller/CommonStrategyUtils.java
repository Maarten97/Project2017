package controller;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import model.Board;

/**
 * Class with common player methods and utils.
 * 
 * @author Maarten Looijenga en Thomas Hogema
 */
public class CommonStrategyUtils {

	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns a set of all free fields.
	 * 
	 * @param b Board to find empty field from.
	 * @return Set with all free indexes
	 */
	//@ requires board != null; 
	public static Set<int[]> getFreeFields(Board b) {
		Set<int[]> randomFreeCoordinates = new HashSet<>();
		for (int x = 0; x < Board.DIM; x++) {
			for (int y = 0; y < Board.DIM; y++) {
				for (int z = 0; z < Board.DIM; z++) {
					if (b.isEmptyField(x, y, z)) {
						randomFreeCoordinates.add(new int[]{x, y, z});
					}
				}
			}
		}
		return randomFreeCoordinates;
	}
	
	/**
	 * Get a random empty field.
	 * 
	 * @param b board to get free coordinates from
	 * @return the coordinates of a random empty field in an int array
	 */
	// @ requires board != null;
	public static int[] getRandomFreeField(Board b) {
		Set<int[]> freeFieldIndexes = getFreeFields(b);

		// Picks a random field from the list
		int[] coordinate = new int[3];
		int randomValue = new Random().nextInt(freeFieldIndexes.size());
		// make up a random number within the range of the set.
		int i = 0;
		for (int[] a : freeFieldIndexes) {
			if (i == randomValue) {
				coordinate = a;
			}
			i++;
		}
		int[] xycoordinate = new int[]{coordinate[0], coordinate[2]};
		return xycoordinate;
	}

}
