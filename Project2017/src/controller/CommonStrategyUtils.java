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
	 * Get a random empty field index.
	 * 
	 * @param b
	 *            board to get free index from
	 * @return the index of a random empty field
	 */
	public static int getRandomFreeField(Board b) {
		// Gets a list of empty fields
		Set<Integer> freeFieldIndexes = new HashSet<Integer>();
		int fieldCount = b.getFields().length;
		for (int i = 0; i < fieldCount; i++) {
			if (b.isEmptyField(i)) {
				freeFieldIndexes.add(i);
			}
		}

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
