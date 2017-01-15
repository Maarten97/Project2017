package model;



/**
 * Board of the 3D 4 in a row game.
 * 
 * @author Thomas Hogema en Maarten Looijenga
 * @version 1.0
 *
 */
public class Board {

	public static final int DIM = 4;
	
	/**
	 * The DIM by DIM by DIM fields of the game. 
	 */
	// @ private invariant fields.length == DIM*DIM*DIM;
	/*
	 * @ invariant (\forall int i; 0 <= i & i < DIM*DIM; getField(i) ==
	 * Mark.EMPTY || getField(i) == Mark.XX || getField(i) == Mark.OO);
	 */
	private Mark[] fields;
	
	/**
	 * Creates a list with the fields of a game.
	 */
	
	// @ ensures (\forall int i; 0 <= i & i < DIM * DIM * DIM; this.getField(i) ==
	// Mark.EMPTY);
	public Board() {
		fields = new Mark[DIM * DIM * DIM];
		reset();
	}
	
	/**
	 * Creates a deep copy of this field.
	 */
	/*
	 * @ ensures \result != this; ensures (\forall int i; 0 <= i & i < DIM *
	 * DIM * DIM; \result.getField(i) == this.getField(i));
	 * 
	 */ 
	public Board deepCopy() {
		Board deepboard = new Board();
		for (int i = 0; i < DIM * DIM * DIM; i++) {
			deepboard.fields[i] = this.fields[i];
		}
		return deepboard;
	}
	/**
	 * Calculates the index in the linear array of fields from a collection (row, col, leven).
	 * 
	 * 
	 * @return the index belonging to the (row,col,level)-field
	 */
	// @ requires 0 <= row & row < DIM;
	// @ requires 0 <= col & col < DIM;
	// @ requires 0 <= level & level < DIM;
	/* @pure */
	public int index(int row, int col, int level) {
		return row * DIM + col + level * DIM * DIM;
	}
	
	/**
	 * Returns true if i is a valid index of a field on the board.
	 * 
	 * @return true if 0 <= index < DIM*DIM*DIM
	 */
	// @ ensures \result == (0 <= index && index < DIM * DIM * DIM);
	/* @pure */
	public boolean isField(int index) {
		if (index >= 0 && index < DIM * DIM * DIM) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true if the (row,col,level) collection refers to a valid field on the
	 * board.
	 *
	 * @return true if 0 <= row < DIM && 0 <= col < DIM && 0 <= level < DIM
	 */
	// @ ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM && 0 <= level && level < DIM) ;
	/* @pure */
	public boolean isField(int row, int col, int level) {
		return isField(index(row, col, level));

	}
	
	private void reset() {
		// TODO Auto-generated method stub
		
	}

}
