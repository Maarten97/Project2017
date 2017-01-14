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
	
	
	
	
	private void reset() {
		// TODO Auto-generated method stub
		
	}

}
