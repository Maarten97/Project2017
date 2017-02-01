package model;

/**
 * Board of the 3D 4 in a row game.
 * 
 * @author Thomas Hogema en Maarten Looijenga
 */
public class Board {
	// -- Instance variables -----------------------------------------
	
	public static final int DIM = 4;

	/**
	 * The DIM by DIM by DIM fields of the game.
	 */
	/* @ private invariant fields.length == DIM*DIM*DIM;
	 * @ invariant (\forall int i; 0 <= i & i < DIM*DIM; getField(i) ==
	 * Mark.EMPTY || getField(i) == Mark.XX || getField(i) == Mark.OO);
	 */
	private Mark[][][] fields;

	// -- Constructors -----------------------------------------------
	
	/**
	 * Creates an empty board, and a list with the fields of a game.
	 */
	// @ ensures (\forall int i; 0 <= i & i < DIM * DIM * DIM; this.getField(i) == Mark.EMPTY);
	public Board() {
		fields = new Mark[DIM][DIM][DIM];
		reset();
	}

	// -- Queries/Commands ----------------------------------------------------
	/**
	 * Creates a deep copy of this field.
	 * 
	 * @return Deepcopy of the board.
	 */
	/*
	 * @ ensures \result != this; ensures (\forall int i; 0 <= i & i < DIM * DIM
	 * * DIM; \result.getField(i) == this.getField(i));
	 */
	public Board deepCopy() {
		Board deepboard = new Board();
		for (int x = 0; x < DIM; x++) {
			for (int y = 0; y < DIM; y++) {
				for (int z = 0; z < DIM; z++) {
					deepboard.fields[x][y][z] = this.fields[x][y][z];
				}
			}

		}
		return deepboard;
	}

	/**
	 * Calculates the index in the linear array of fields from a collection
	 * (row, col, level).
	 * 
	 * @return the index belonging to the (row,col,level)-field
	 */
	/* @ requires 0 <= row & row < DIM;
	 * @ requires 0 <= col & col < DIM;
	 * @ requires 0 <= level & level < DIM;
	 */
	/* @pure */
	public int index(int x, int z, int y) {
		if (x >= 0 & z >= 0 & y >= 0 && x < DIM && z < DIM && y < DIM) {
			return x * DIM + z + y * DIM * DIM;
		} else {
			System.err.println("IndexOutOfBount!");
		}
		return -1;

	}

	/**
	 * Returns true if the (row,col,level) collection refers to a valid field on
	 * the board.
	 *
	 * @return true if 0 <= row < DIM && 0 <= col < DIM && 0 <= level < DIM
	 */
	/*
	 * @ ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM && 0
	 * <= level && level < DIM) ;
	 */
	/* @pure */	public boolean isField(int row, int col, int level) {
		if (row >= 0 & col >= 0 & level >= 0 && row < DIM && col < DIM && level < DIM) {
			return true;
		}
		return false;
	}

	/**
	 * Returns the content of the field referred to by the (row,col) pair.
	 *
	 * @param row the row of the field
	 * @param col the column of the field
	 * @param level the height(or level) of the field.
	 * @return the mark on the field
	 */
	/* @ requires this.isField(row,col,level);
	 * @ ensures \result == Mark.EMPTY || \result == Mark.XX || \result == Mark.OO;
	 */
	/* @pure */	public Mark getField(int row, int col, int level) {
		return fields[row][level][col];

	}

	/**
	 * Returns true if the field referred to by the (row,col) pair it empty.
	 *
	 * @param row the row of the field
	 * @param col the column of the field
	 * @param level the height(or level) of the field.
	 * @return true if the field is empty
	 * @throws FieldNotExsistException
	 */
	// @ requires this.isField(row,col);
	// @ ensures \result == (this.getField(row,col) == Mark.EMPTY);
	/* @pure */ public boolean isEmptyField(int row, int col, int level) {
		if (isField(row, col, level)) {
			return fields[row][level][col] == Mark.EMPTY;
		}
		return false;
	}

	/**
	 * Checks if the given move is valid; if there are no 4 tiles on the same X
	 * and Z value. return true if valid, false if not
	 */
	/* @ pure */ public boolean validMove(int x, int z) {
		if (x >= 0 && x < DIM && z >= 0 && z < DIM) {
			return isEmptyField(x, z, dropDown(x, z));
		}
		return false;
	}

	/**
	 * Checks if the mark m has won. A mark wins if it controls at least one
	 * row, column or diagonal.
	 *
	 * @param m the mark of interest
	 * @return true if the mark has won
	 */
	// @ requires m == Mark.XX || m == Mark.OO;
	public boolean isWinner(Mark m) {
		if (hasColumn(m)) {
			return true;
		} else if (hasRow(m)) {
			return true;
		} else if (hasLevel(m)) {
			return true;
		} else if (hasPlaneDiagonal(m)) {
			return true;
		} else if (hasVerticalDiagonal(m)) {
			return true;
		} else if (hasLevelDiagonal(m)) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Checks whether there is a row which is full and only contains the mark m.
	 * 
	 * @param m the mark of interest
	 * @return true if there is a row controlled by m
	 */
	// @ requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */public boolean hasRow(Mark m) {
		for (int level = 0; level < DIM; level++) {
			for (int row = 0; row < DIM; row++) {
				boolean hasRow = true;
				for (int col = 0; col < DIM; col++) {
					if (getField(row, col, level) != m) {
						hasRow = false;
					}
				}
				if (hasRow) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether there is a column which is full and only contains the mark m.
	 * 
	 * @param m the mark of interest
	 * @return true if there is a column controlled by m
	 */
	// @ requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */ public boolean hasColumn(Mark m) {
		for (int level = 0; level < DIM; level++) {
			for (int column = 0; column < DIM; column++) {
				boolean hasColumn = true;
				for (int row = 0; row < DIM; row++) {
					if (getField(row, column, level) != m) {
						hasColumn = false;
					}
				}
				if (hasColumn) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether there is a level which is full and only contains the mark m.
	 * 
	 * @param m the mark of interest
	 * @return true if there is a level controlled by m
	 */
	// @ requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */ public boolean hasLevel(Mark m) {
		for (int col = 0; col < DIM; col++) {
			for (int row = 0; row < DIM; row++) {
				boolean hasLevel = true;
				for (int level = 0; level < DIM; level++) {
					if (getField(row, col, level) != m) {
						hasLevel = false;
					}
				}
				if (hasLevel) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether there is a diagonal which is full and only contains the mark m.
	 * 
	 * @param m the mark of interest
	 * @return true if there is a diagonal controlled by m
	 */
	// @ requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasPlaneDiagonal(Mark m) {
		Boolean hasDiagonal = true;
		for (int level = 0; level < DIM; level++) {
			// linksboven --> rechtsonder
			hasDiagonal = true;
			for (int i = 0; i < DIM; i++) {
				if (getField(i, i, level) != m) {
					hasDiagonal = false;
				}
			}
			if (hasDiagonal) {
				return true;
			}
			//linksonder --> rechtsboven
			hasDiagonal = true;
			for (int j = 0; j < DIM; j++) {
				if (getField(DIM - j - 1, j, level) != m) {
					hasDiagonal = false;
				}
			}
			if (hasDiagonal) {
				return true;
			}
		}
		return false;
	}
	

	/**
	 * Tests if there is one of 4 possible vertical diagonals.
	 * 
	 * @param m the mark to check
	 * @return true if there is at least one vertical diagonal.
	 */
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasVerticalDiagonal(Mark m) {
		return hasXXXDiagonal(m) || hasXYXDiagonal(m) || hasYXXDiagonal(m) || hasYYXDiagonal(m);
	}

	/**
	 * Checks whether there is a vertical diagonal from top left to right bottom.
	 * Tests 000, 111, 222, 333 (with DIM ==4)
	 * 
	 * @param m the mark of interest.
	 * @return true if the diagonal is occupied by m.
	 */ 
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasXXXDiagonal(Mark m) {
		boolean diagonal = true;
		for (int i = 0; i < DIM; i++) {
			if (getField(i, i, i) != m) {
				diagonal = false;
			}
		}
		return diagonal;
	}

	/**
	 * Checks whether there is a vertical diagonal from top right to left bottom.
	 * Tests 030, 121, 212, 303 (with DIM ==4)
	 * 
	 * @param m the mark of interest.
	 * @return true if the diagonal is occupied by m.
	 */ 
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasXYXDiagonal(Mark m) {
		boolean diagonal = true;
		for (int i = 0; i < DIM; i++) { 
			if (!getField(i, DIM - i - 1, i).equals(m)) {
				diagonal = false;
			}
		}
		return diagonal;
	}

	/**
	 * Checks whether there is a vertical diagonal from bottom left to right top.
	 * Tests 300, 211, 122, 033 (with DIM ==4)
	 * 
	 * @param m the mark of interest.
	 * @return true if the diagonal is occupied by m.
	 */ 
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasYXXDiagonal(Mark m) {
		boolean diagonal = true;
		for (int i = 0; i < DIM; i++) { 
			if (!getField(DIM - i - 1, i, i).equals(m)) {
				diagonal = false;
			}
		}
		return diagonal;
	}
	
	/**
	 * Checks whether there is a vertical diagonal from bottom right to left top.
	 * Tests 330, 221, 112, 003 (with DIM ==4)
	 * 
	 * @param m the mark of interest.
	 * @return true if the diagonal is occupied by m.
	 */ 
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasYYXDiagonal(Mark m) {
		boolean diagonal = true;
		for (int i = 0; i < DIM; i++) { 
			if (!getField(DIM - i - 1, DIM - i - 1, i).equals(m)) {
				diagonal = false;
			}
		}
		return diagonal;
	}

	
	/**
	 * Test for all 4 (x4) possibilities if there is a diagonal between column and level.
	 * 
	 * @param m the mark to check for.
	 * @return true is Mark m has a complete diagonal on column and level.
	 */
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasLevelDiagonal(Mark m) {
		return hasLevelDiagonalTopBottom(m) || hasLevelDiagonalBottomTop(m) ||
				hasLevelDiagonalLeftRight(m) || hasLevelDiagonalRightLeft(m);
	}
	
	/**
	 * Tests for every column if there is a diagonal between row and level from top to bottom.
	 * 
	 * @param m the mark to check for
	 * @return true if Mark m holds a complete diagonal
	 */
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasLevelDiagonalTopBottom(Mark m) {
		for (int column = 0; column < DIM; column++) {
			boolean hasDiagonal = true;
			for (int i = 0; i < DIM; i++) {
				if (getField(i, column, i) != m) {
					hasDiagonal = false;
				}
			}
			if (hasDiagonal == true) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Tests for every column if there is a diagonal between row and level from bottom to top.
	 * 
	 * @param m the mark to check for
	 * @return true if Mark m holds a complete diagonal
	 */
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasLevelDiagonalBottomTop(Mark m) {
		for (int column = 0; column < DIM; column++) {
			boolean hasDiagonal = true;
			for (int i = 0; i < DIM; i++) {
				if (getField(DIM - i - 1, column, i) != m) {
					hasDiagonal = false;
				}
			}
			if (hasDiagonal == true) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Tests for every row if there is a diagonal between row and level from left to right.
	 * 
	 * @param m the mark to check for
	 * @return true if Mark m holds a complete diagonal
	 */
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasLevelDiagonalLeftRight(Mark m) {
		for (int row = 0; row < DIM; row++) {
			boolean hasDiagonal = true;
			for (int i = 0; i < DIM; i++) {
				if (getField(row, i, i) != m) {
					hasDiagonal = false;
				}
			}
			if (hasDiagonal == true) {
				return true;
			}
		}
		return false;
	}
			
	/**
	 * Tests for every row if there is a diagonal between row and level from right to left.
	 * 
	 * @param m the mark to check for
	 * @return true if Mark m holds a complete diagonal
	 */
	// @requires Mark m == Mark.XX || Mark m == Mark.OO;
	/* @ pure */
	public boolean hasLevelDiagonalRightLeft(Mark m) {
		for (int row = 0; row < DIM; row++) {
			boolean hasDiagonal = true;
			for (int i = 0; i < DIM; i++) {
				if (getField(row, i, DIM - i - 1) != m) {
					hasDiagonal = false;
				}
			}
			if (hasDiagonal == true) {
				return true;
			}
		}
		return false;
	}
	

	/**
	 * Tests if the whole board is full.
	 *
	 * @return true if all fields are occupied
	 */
	// @ ensures \result == (\forall int i; i <= 0 & i < DIM * DIM * DIM;
	// this.getField(i) != Mark.EMPTY);
	/* @pure */ public boolean isFull() {
		for (int x = 0; x < DIM; x++) {
			for (int y = 0; y < DIM; y++) {
				for (int z = 0; z < DIM; z++) {
					if (fields[x][y][z].equals(Mark.EMPTY)) {
						return false;
					}
				}
			}
		}
		return true;
	}

	/**
	 * Empties all fields of this board; places an empty tile at all fields
	 */
	/*
	 * @ ensures (\forall int i; 0 <= i & i < DIM * DIM * DIM; this.getField(i)
	 * == Mark.EMPTY); @
	 */
	public void reset() {
		for (int x = 0; x < DIM; x++) {
			for (int y = 0; y < DIM; y++) {
				for (int z = 0; z < DIM; z++) {
					fields[x][y][z] = Mark.EMPTY;

				}
			}
		}
	}

	/**
	 * Sets the content of the field represented by the (row, column, level)
	 * collection to the mark m.
	 * 
	 * @param row the field's row
	 * @param col the field's column
	 * @param level the height(or level) of the field.
	 * @param m the mark to be placed
	 */
	// @ requires this.isField(row,col,level);
	// @ requires Mark m == Mark.XX || Mark m == Mark.OO;
	// @ ensures this.getField(row,col,level) == m;
	public void setField(int row, int col, int level, Mark m) {
		if (this.isField(row, col, level)) {
			fields[row][level][col] = m;
		}

	}

	/**
	 * Sets the content of the field represented by the (row, column)
	 * collection to the mark m, level will be calculated by the 
	 * dropdown method.
	 * 
	 * @param row the field's row
	 * @param col the field's column
	 * @param m the mark to be placed
	 */
	// @ requires Mark m == Mark.XX || Mark m == Mark.OO;
	// @ requires 0 <= row & row < DIM;
	// @ requires 0 <= col & col < DIM;
	// @ ensures this.getField(row,col,dropDown(row,col) == m;
	public void setField(int row, int col, Mark m) {
		int level = dropDown(row, col);
		setField(row, col, level, m);
	}

	/**
	 * This method puts the stone on the lowest level as possible.
	 * @param row the field's row
	 * @param col the field's column
	 * @return lowest index as possible for given row and col.
	 */
	// @ requires 0 <= row & row < DIM;
	// @ requires 0 <= col & col < DIM;
	// @ ensures \result >= 0 && \result <=DIM;
	public int dropDown(int row, int col) {
		for (int i = 3; i > 0; i--) {
			if (!isEmptyField(row, col, i - 1)) {
				return i;
			}
		}
		return 0;
	}

	/**
	 * To String for board. Prints the 4 levels of board.
	 */
	/*@ pure */
	public String toString() {
		// first info line
		String board = "";
		for (int i = 0; i < DIM; i++) {
			board = board + "Level: " + i + "                ";
		}
		// Enter/return after level indications:
		board = board + "\n";

		// Lines of the board itself. One line per Y level.
		for (int y = 0; y < DIM; y++) {
			// Per level
			for (int l = 0; l < DIM; l++) {
				// All 4 X values
				String row = "";
				for (int x = 0; x < DIM; x++) {
					row = row + getField(y, x, l).toShortString() + " ";
				}
				// Spaces for Next level:
				board = board + row + "        ";
			}
			// Enter/return after the first row of levels:
			board = board + "\n";
		}
		return board;
	}
}
