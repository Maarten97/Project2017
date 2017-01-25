package model;

/**
 * Board of the 3D 4 in a row game.
 * 
 * @author Thomas Hogema en Maarten Looijenga
 * @version 1.0
 *
 */
public class Board {
	// TODO Still have to change the JML and the Javadoc and separate queries and commands

	// -- Instance variables -----------------------------------------
	public static final int DIM = 4;

	/**
	 * The DIM by DIM by DIM fields of the game.
	 */
	// @ private invariant fields.length == DIM*DIM*DIM;
	/*
	 * @ invariant (\forall int i; 0 <= i & i < DIM*DIM; getField(i) ==
	 * Mark.EMPTY || getField(i) == Mark.XX || getField(i) == Mark.OO);
	 */
	private Mark[][][] fields;

	
	// -- Constructors -----------------------------------------------
	/**
	 * Creates an empty board, and a list with the fields of a game.
	 */

	// @ ensures (\forall int i; 0 <= i & i < DIM * DIM * DIM; this.getField(i)
	// ==
	// Mark.EMPTY);
	public Board() {
		fields = new Mark[DIM][DIM][DIM];
		reset();
	}

	// -- Queries/Commands ----------------------------------------------------
	/**
	 * Creates a deep copy of this field.
	 */
	/*
	 * @ ensures \result != this; ensures (\forall int i; 0 <= i & i < DIM * DIM
	 * * DIM; \result.getField(i) == this.getField(i));
	 * 
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
	// @ requires 0 <= row & row < DIM;
	// @ requires 0 <= col & col < DIM;
	// @ requires 0 <= level & level < DIM;
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
	/* @pure */
	public boolean isField(int row, int col, int level) {
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
	// @ requires this.isField(row,col,level);
	// @ ensures \result == Mark.EMPTY || \result == Mark.XX || \result ==
	// Mark.OO;
	/* @pure */
	public Mark getField(int row, int col, int level) {
		return fields[row][level][col];

	}

	/**
	 * Returns true if the field referred to by the (row,col) pair it empty.
	 *
	 * @param row the row of the field
	 * @param col the column of the field
	 * @param level the height(or level) of the field.
	 * @return true if the field is empty
	 */
	// @ requires this.isField(row,col);
	// @ ensures \result == (this.getField(row,col) == Mark.EMPTY);
	/* @pure */
	public boolean isEmptyField(int row, int col, int level) {
		if (isField(row, col, level)) {
			if (fields[row][level][col] == Mark.EMPTY) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Checks if the given move is valid; if there are no 4 tiles on the same X and Z value.
	 *return true if valid, false if not
	 */
	/* @ pure */public boolean validMove(int x, int z) {
		if (x >= 0 && x < DIM && z >= 0 && z < DIM) {
			return isEmptyField(x, z, dropDown(x, z));
		}
		return false;
	}

	/**
	 * Checks whether there is a row which is full and only contains the mark m.
	 * 
	 * @param m the mark of interest
	 * @return true if there is a row controlled by m
	 */
	/* @ pure */public boolean hasRow(Mark m) {
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
	 * Checks whether there is a column which is full and only contains the mark m.
	 * @param m the mark of interest
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

	// Does this work and can it be done better/more efficient?
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
		// TODO Has to be implemented.
		return false;
	}

	/**
	 * Tests if the whole board is full.
	 *
	 * @return true if all fields are occupied
	 */
	// @ ensures \result == (\forall int i; i <= 0 & i < DIM * DIM * DIM;
	// this.getField(i) != Mark.EMPTY);
	/* @pure */
	public boolean isFull() {
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
	 * Sets the content of the field represented by the (row,col,level)
	 * collection to the mark m.
	 * 
	 * @param row the field's row
	 * @param col the field's column
	 * @param level the height(or level) of the field.
	 * @param m the mark to be placed
	 */
	// @ requires this.isField(row,col,level);
	// @ ensures this.getField(row,col,level) == m;
	public void setField(int row, int col, int level, Mark m) {
		if (this.isField(row, col, level)) {
			fields[row][level][col] = m;
		}

	}

	public void setField(int row, int col, Mark m) {
		int level = dropDown(row, col);
		setField(row, col, level, m);
	}

	// TODO nog testen!!! checken of 4 leeg is!
	public int dropDown(int row, int col) {
		for (int i = 4; i > 0; i--) {
			if (!isEmptyField(row, col, i - 1)) {
				return i;
			}
		}
		return 0;
	}

	/**
	 * To String for board. Prints the board in 8 different ways.
	 */
	public String toString() {
		//first info line 
		String board = "";
		for (int i = 0; i < DIM; i++) {
			board = board + "Level: " + i + "                ";
		}
		//Enter/return after level indications:
		board = board + "\n";
		
		//Lines of the board itself. One line per Y level.
		for (int y = 0; y < DIM; y++) {
			//Per level
			for (int l = 0; l < DIM; l++) {
				//All 4 X values
				String row = "";
				for (int x = 0; x < DIM; x++) {
					row = row + getField(y, x, l).toShortString() + " ";
				}
				//Spaces for Next level:
				board = board + row + "        ";
			}
			//Enter/return after the first row of levels:
			board = board + "\n";
		}
		return board;
		
		
		
		
		/* per level:
		String level = "";
		for (int k = 0; k < 4; k++) {
			if (k > 0) {
				level = level + "\n";
			}
			level = level + "Level: " + k + "\n";
			
			for (int j = 0; j < 4; j++) {
				String row = "";
				for (int i = 0; i < 4; i++) {
					row = row + getField(i, j, k).toShortString() + " ";
				}
				level = level + row + "\n";
			}
		}
		return level;
	*/
	}
}
