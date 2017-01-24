package controller;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import model.Board;

/**
 * Class with common player methods and utils.
 */
public class CommonStrategyUtils {

	/**
	 * Returns a set of all free fields
	 * @param b Board to find empty field from.
	 * @return Set with all free indexes
	 */
	/*@ requires board != null; 
	 */
	public static Set<Integer> getFreeFields(Board b) {
		Set<Integer> freeFieldIndexes = new HashSet<Integer>();
		int fieldCount = Board.DIM * Board.DIM * Board.DIM - 1;
		for (int i = 0; i < fieldCount; i++) {
			if (b.isEmptyField(i)) {
				freeFieldIndexes.add(i);
			}
		}
		return freeFieldIndexes;
		
	}
	
	/**
	 * Get a random empty field index.
	 * @param b board to get free index from
	 * @return the index of a random empty field
	 */
	/* @ requires board != null; 
	 */
	public static int getRandomFreeField(Board b) {
		Set<Integer> freeFieldIndexes = getFreeFields(b);

		// Picks a random field from the list
		Integer randomFreeIndex = new Integer(-1);
		int randomValue = new Random().nextInt(freeFieldIndexes.size());
		// make up a random number within the range of the set.
		int i = 0;
		for (Integer a : freeFieldIndexes) {
			if (i == randomValue) {
				randomFreeIndex = a;
			}
			i++;
		}
		return randomFreeIndex.intValue();
	}

}
