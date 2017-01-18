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
		if (row >= 0 & col >= 0 & level >= 0 && row < DIM && col < DIM && level < DIM) {
			return row * DIM + col + level * DIM * DIM;
		} else {
			System.err.println("IndexOutOfBount!");
		}
		return -1;

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
	/*
	 *  @ ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM 
	 *  && 0 <= level && level < DIM) ;
	 */
	/* @pure */
	public boolean isField(int row, int col, int level) {
		return isField(index(row, col, level));

	}
	
	/**
	 * Returns the content of the field i.
	 *
	 * @param i  
	 * 			The index of the requested field on the board.
	 *            
	 * @return The mark on the field.
	 */
	// @ requires this.isField(i);
	// @ ensures \result == Mark.EMPTY || \result == Mark.XX || \result ==
	// Mark.OO;
	/* @pure */
	public Mark getField(int i) {
		if (isField(i)) {
			return fields[i];
		}
		return null;
	}
	
	/**
	 * Returns the content of the field referred to by the (row,col) pair.
	 *
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @param level 
	 * 			the hight(or level) of the field.          
	 * @return the mark on the field
	 */
	// @ requires this.isField(row,col,level);
	// @ ensures \result == Mark.EMPTY || \result == Mark.XX || \result ==
	// Mark.OO;
	/* @pure */
	public Mark getField(int row, int col, int level) {
		return getField(index(row, col, level));

	}
	/**
	 * Returns true if the field i is empty.
	 *
	 * @param i
	 *            the index of the field.
	 * @return true if the field is empty
	 */
	// @ requires this.isField(i);
	// @ ensures \result == (this.getField(i) == Mark.EMPTY);
	/* @pure */
	public boolean isEmptyField(int i) {
		if (isField(i)) {
			if (fields[i] == Mark.EMPTY) {
				return true;
			} 
		} 
		return false;
	}

	/**
	 * Returns true if the field referred to by the (row,col) pair it empty.
	 *
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @param level 
	 * 			  the hight(or level) of the field. 
	 *  
	 * @return true if the field is empty
	 */
	// @ requires this.isField(row,col);
	// @ ensures \result == (this.getField(row,col) == Mark.EMPTY);
	/* @pure */
	public boolean isEmptyField(int row, int col, int level) {
		return isEmptyField(index(row, col, level));
	}
	
	/**
	 * Returns true if the game is over. The game is over when there is a winner.
	 * In this game, it is not possible to get a draw.
	 *
	 * @return true if the game is over
	 */
	// @ ensures \result == this.hasWinner();
	/* @pure */
	public boolean gameOver() {
		return this.hasWinner();
	}
	
	/**
	 * Checks whether there is a row which is full and only contains the mark m.
	 *
	 * @param m
	 *            the mark of interest
	 * @return true if there is a row controlled by m
	 */
	/* @ pure */
	public boolean hasRow(Mark m) {
		boolean row = true;
		for (int level = 0; level < DIM; level++) {
			for (int i = 0; i < DIM; i++) {
				for (int col = 0; col < DIM; col++) {
					if (getField(i, col, level) != m) {
						row = false;
					}
				}
			}
			if (row) {
				return true;
			}

		}
		return false;
	}

	/**
	 * Checks whether there is a column which is full and only contains the mark
	 * m.
	 *
	 * @param m
	 *            the mark of interest
	 * @return true if there is a column controlled by m
	 */
	/* @ pure */
	public boolean hasColumn(Mark m) {
		boolean column = true;
		for (int level = 0; level < DIM; level++) {
			for (int i = 0; i < DIM; i++) {
				for (int row = 0; row < DIM; row++) {
					if (getField(row, i, level) != m) {
						column = false;
					}
				}
			}
			if (column) {
				return true;

			}
		}
		return false;
	}
	
	public boolean hasLevel(Mark m) {
		boolean level = true;
		for (int col = 0; col < DIM; col++) {
			for (int i = 0; i < DIM; i++) {
				for (int row = 0; row < DIM; row++) {
					if (getField(row, col, i) != m) {
						level = false;
					}
				}
			}
			if (level) {
				return true;
			}
		}
		return false;
	}
	
	//Does this work and can it be done better/more efficient?
	public boolean hasPlaneDiagonal(Mark m) {
		int numberHits = 0;
		int dRow = 0;
		int dColumn = 0;
		for (int level = 0; level < DIM; level++) {
			while (dRow < DIM) {
				if (getField(dRow, dColumn, level).equals(m)) {
					numberHits++;
					dRow++;
					dColumn++;
				} else {
					break;
				}
			}
			if (numberHits == DIM) {
				return true;
			} else {
				numberHits = 0;
				dRow = DIM - 1;
				dColumn = 0;
				while (dColumn < DIM) {
					if (getField(dRow, dColumn, level).equals(m)) {
						numberHits++;
						dRow--;
						dColumn++;
					} else {
						break;
					}
				}
				if (numberHits == DIM) {
					return true;
				}
			}
		}
		return false;
	}
	public boolean hasVerticalDiagonal(Mark m) {
		//TODO Has to be implemented.
		return false;
	}
	/**
	 * Checks if the mark m has won. A mark wins if it controls at least one
	 * row, column or diagonal.
	 *
	 * @param m
	 *            the mark of interest
	 * @return true if the mark has won
	 */
	public boolean isWinner(Mark m) {
		if (this.hasColumn(m)) {
			return true;
		} else if (this.hasRow(m)) {
			return true;
		} else if (this.hasPlaneDiagonal(m)) {
			return true;
		} else if (this.hasVerticalDiagonal(m)) {
			return true;
		} else if (this.hasLevel(m)) {
			return true;
		} else {
			return false;
		}
	}
	/**
	 * Returns true if the game has a winner. This is the case when one of the
	 * marks controls at least one row, column or diagonal.
	 *
	 * @return true if the student has a winner.
	 */
	// @ ensures \result == isWinner(Mark.XX) | \result == isWinner(Mark.OO);
	/* @pure */
	public boolean hasWinner() {
		return isWinner(Mark.BLUE) || isWinner(Mark.RED);
	}

	/**
	 * Empties all fields of this student (i.e., let them refer to the value
	 * Mark.EMPTY).
	 */
	/*
	 * @ ensures (\forall int i; 0 <= i & i < DIM * DIM * DIM; this.getField(i) ==
	 * Mark.EMPTY); @
	 */
	public void reset() {
		for (int i = 0; i < DIM * DIM * DIM; i++) {
			fields[i] = Mark.EMPTY;
		}
	}

	/**
	 * Sets the content of field i to the mark m.
	 *
	 * @param i
	 *            the field number 
	 * @param m
	 *            the mark to be placed
	 */
	// @ requires this.isField(i);
	// @ ensures this.getField(i) == m;
	public void setField(int i, Mark m) {
		if (this.isField(i)) {
			fields[i] = m; 
		}
	}

	/**
	 * Sets the content of the field represented by the (row,col,level) collection to the
	 * mark m.
	 *
	 * @param row
	 *            the field's row
	 * @param col
	 *            the field's column
	 * @param level 
	 * 			  the hight(or level) of the field. 
	 * @param m
	 *            the mark to be placed
	 */
	// @ requires this.isField(row,col,level);
	// @ ensures this.getField(row,col,level) == m;
	public void setField(int row, int col, int level, Mark m) {
    	setField(index(row, col, level), m);
	}
	
	public void setField(int row, int col, Mark m){
		int level = dropDown(row, col);
		setField(row, col, level, m);
	}
	
	// TODO nog testen!!!
	public int dropDown(int row, int col) {
		for (int i = 3; i > 0; i--) {
			if (!isEmptyField(row, col, i - 1)) {
				return i;
			}
		}
		return 0;
	}
	
//	public String toString() {
//		return "Please implement this method in class TUI!";
//	}

}
