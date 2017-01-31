package test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import model.*;

public class BoardTest {

	/**
	 * Provides a JUnit test file for the class board. Testclass yields if
	 * board.DIM == 4.
	 * 
	 * @author Maarten Looijenga
	 *
	 */

	private Board board;
	private static final int DIM = 4;

	@Before
	// TODO kan ik ook tiles op board leggen zonder de methode setTiles() te
	// gebruiken?
	public void setUp() throws Exception {
		board = new Board();
		board.setField(0, 0, Mark.OO);
		board.setField(0, 1, Mark.OO);
		board.setField(1, 1, Mark.OO);
		board.setField(2, 1, Mark.OO);
		board.setField(1, 0, Mark.XX);
		board.setField(1, 2, Mark.XX);
		board.setField(2, 2, Mark.XX);
		board.setField(1, 3, Mark.XX);

	}

	@Test
	public void deepCopyTest() {
		System.out.println("originele board: ");
		System.out.println(board.toString());
		System.out.println("Deepcopy: ");
		System.out.println(board.deepCopy().toString());
	}

	@Test
	public void validMoveTest() {
		assertTrue(board.validMove(0, 0));
		assertTrue(board.validMove(3, 3));
		board.setField(0, 0, Mark.OO);
		board.setField(0, 0, Mark.OO);
		board.setField(0, 0, Mark.OO);
		assertFalse(board.validMove(0, 0));
		assertTrue(board.validMove(0, 1));
	}
	
	@Test
	public void indexTest() {
		assertEquals(0, board.index(0, 0, 0));
		assertEquals(25, board.index(2, 1, 1));
		assertEquals(44, board.index(3, 0, 2));
		assertEquals(63, board.index(3, 3, 3));
		assertNotEquals(18, board.index(2, 0, 1));
	}

	@Test
	public void testIsField() {
		assertTrue(board.isField(0, 0, 0));
		assertTrue(board.isField(3, 3, 3));
		assertTrue(board.isField(1, 2, 0));
		assertFalse(board.isField(1, 2, 4));
		assertFalse(board.isField(-1, 2, 3));
		assertFalse(board.isField(1, 10, 0));
	}

	@Test
	public void testGetField() {
		assertEquals(board.getField(0, 0, 0), Mark.OO);
		assertEquals(board.getField(0, 1, 0), Mark.OO);
		assertEquals(board.getField(1, 2, 0), Mark.XX);
		assertEquals(board.getField(3, 0, 1), Mark.EMPTY);
		assertNotEquals(board.getField(0, 3, 0), Mark.OO);
		assertNotEquals(board.getField(3, 3, 1), Mark.OO);
	}

	@Test
	public void testIsEmptyField() {
		assertTrue(board.isEmptyField(3, 3, 3));
		assertTrue(board.isEmptyField(3, 3, 0));
		assertFalse(board.isEmptyField(2, 1, 0));
	}

	@Test
	public void testHasRow() {
		assertFalse(board.hasRow(Mark.OO));
		board.setField(0, 2, Mark.OO);
		board.setField(0, 3, Mark.OO);
		assertFalse(board.hasRow(Mark.XX));
		assertTrue(board.hasRow(Mark.OO));
	}

	@Test
	public void testHasColumn() {
		assertFalse(board.hasColumn(Mark.OO));
		board.setField(3, 1, Mark.OO);
		assertFalse(board.hasColumn(Mark.XX));
		assertTrue(board.hasColumn(Mark.OO));
	}

	@Test
	public void testHasLevel() {
		assertFalse(board.hasLevel(Mark.XX));
		assertFalse(board.hasLevel(Mark.OO));
		board.setField(1, 3, Mark.XX);
		board.setField(1, 3, Mark.XX);
		board.setField(1, 3, Mark.XX);
		assertFalse(board.hasLevel(Mark.OO));
		assertTrue(board.hasLevel(Mark.XX));
	}

	@Test
	public void testHasPlaneDiagonal() {
		assertFalse(board.hasPlaneDiagonal(Mark.XX));
		assertFalse(board.hasPlaneDiagonal(Mark.OO));
		board.setField(3, 3, Mark.XX);
		board.setField(3, 3, Mark.XX);
		board.setField(2, 2, Mark.XX);
		board.setField(0, 0, Mark.XX);
		assertFalse(board.hasPlaneDiagonal(Mark.XX));
		board.setField(1, 1, Mark.XX);
		assertFalse(board.hasPlaneDiagonal(Mark.OO));
		assertTrue(board.hasPlaneDiagonal(Mark.XX));
	}

	@Test
	public void testXXXDiagonal() {
		assertFalse(board.hasXXXDiagonal(Mark.OO));
		board.setField(2, 2, Mark.XX);
		board.setField(3, 3, Mark.XX);
		board.setField(3, 3, Mark.XX);
		board.setField(3, 3, Mark.XX);
		board.setField(3, 3, Mark.OO);
		board.setField(2, 2, Mark.OO);
		board.setField(1, 1, Mark.OO);
		assertFalse(board.hasXXXDiagonal(Mark.XX));
		assertTrue(board.hasXXXDiagonal(Mark.OO));
		assertTrue(board.hasVerticalDiagonal(Mark.OO));
	}

	@Test
	public void testXYXDiagonal() {
		assertFalse(board.hasXYXDiagonal(Mark.OO));
		board.setField(0, 3, Mark.XX);
		board.setField(3, 0, Mark.OO);
		board.setField(3, 0, Mark.OO);
		board.setField(3, 0, Mark.OO);
		board.setField(3, 0, Mark.OO);
		board.setField(3, 0, Mark.XX);
		board.setField(1, 2, Mark.XX);
		board.setField(2, 1, Mark.XX);
		board.setField(2, 1, Mark.XX);
		board.setField(3, 0, Mark.XX);
		assertFalse(board.hasXYXDiagonal(Mark.OO));
		assertTrue(board.hasXYXDiagonal(Mark.XX));
		assertTrue(board.hasVerticalDiagonal(Mark.XX));
	}

	@Test
	public void testYXXDiagonal() {
		assertFalse(board.hasYXXDiagonal(Mark.OO));
		board.setField(0, 3, Mark.OO);
		board.setField(0, 3, Mark.OO);
		board.setField(0, 3, Mark.OO);
		board.setField(0, 3, Mark.XX);
		board.setField(1, 2, Mark.OO);
		board.setField(1, 2, Mark.XX);
		board.setField(2, 1, Mark.XX);
		board.setField(3, 0, Mark.XX);
		assertFalse(board.hasYXXDiagonal(Mark.OO));
		assertTrue(board.hasYXXDiagonal(Mark.XX));
		assertTrue(board.hasVerticalDiagonal(Mark.XX));
	}

	@Test
	public void testYYXDiagonal() {
		assertFalse(board.hasYYXDiagonal(Mark.OO));
		board.setField(1, 1, Mark.XX);
		board.setField(0, 0, Mark.XX);
		board.setField(0, 0, Mark.XX);
		board.setField(3, 3, Mark.OO);
		board.setField(2, 2, Mark.OO);
		board.setField(1, 1, Mark.OO);
		board.setField(0, 0, Mark.OO);
		assertFalse(board.hasYYXDiagonal(Mark.XX));
		assertTrue(board.hasYYXDiagonal(Mark.OO));
		assertTrue(board.hasVerticalDiagonal(Mark.OO));
	}


	@Test
	public void testLevelDiagonalTopBottom() {
		assertFalse(board.hasLevelDiagonal(Mark.OO));
		assertFalse(board.hasLevelDiagonalTopBottom(Mark.OO));
		board.setField(2, 0, Mark.XX);
		board.setField(2, 0, Mark.XX);
		board.setField(3, 0, Mark.XX);
		board.setField(3, 0, Mark.XX);
		board.setField(3, 0, Mark.XX);
		board.setField(3, 0, Mark.OO);
		board.setField(2, 0, Mark.OO);
		board.setField(1, 0, Mark.OO);
		assertFalse(board.hasLevelDiagonal(Mark.XX));
		assertTrue(board.hasLevelDiagonal(Mark.OO));
		assertTrue(board.hasLevelDiagonalTopBottom(Mark.OO));
	}

	@Test
	public void testLevelDiagonalLeftRight() {
		assertFalse(board.hasLevelDiagonal(Mark.OO));
		assertFalse(board.hasLevelDiagonalLeftRight(Mark.OO));
		board.setField(0, 2, Mark.XX);
		board.setField(0, 2, Mark.XX);
		board.setField(0, 3, Mark.XX);
		board.setField(0, 3, Mark.XX);
		board.setField(0, 3, Mark.XX);
		board.setField(0, 3, Mark.OO);
		board.setField(0, 2, Mark.OO);
		board.setField(0, 1, Mark.OO);
		assertFalse(board.hasLevelDiagonal(Mark.XX));
		assertTrue(board.hasLevelDiagonal(Mark.OO));
		assertTrue(board.hasLevelDiagonalLeftRight(Mark.OO));
	}

	@Test
	public void testLevelDiagonalBottomTop() {
		assertFalse(board.hasLevelDiagonal(Mark.OO));
		assertFalse(board.hasLevelDiagonalBottomTop(Mark.OO));
		board.setField(1, 2, Mark.XX);
		board.setField(0, 2, Mark.XX);
		board.setField(0, 2, Mark.XX);
		board.setField(0, 2, Mark.XX);
		board.setField(0, 2, Mark.OO);
		board.setField(1, 2, Mark.OO);
		board.setField(2, 2, Mark.OO);
		board.setField(3, 2, Mark.OO);
		assertFalse(board.hasLevelDiagonal(Mark.XX));
		assertTrue(board.hasLevelDiagonal(Mark.OO));
		assertTrue(board.hasLevelDiagonalBottomTop(Mark.OO));
	}

	@Test
	public void testLevelDiagonalRightLeft() {
		assertFalse(board.hasLevelDiagonal(Mark.OO));
		assertFalse(board.hasLevelDiagonalRightLeft(Mark.OO));
		board.setField(2, 0, Mark.XX);
		board.setField(2, 0, Mark.XX);
		board.setField(2, 0, Mark.XX);
		board.setField(2, 1, Mark.XX);
		board.setField(0, 2, Mark.XX);
		board.setField(2, 0, Mark.OO);
		board.setField(2, 1, Mark.OO);
		board.setField(2, 2, Mark.OO);
		board.setField(2, 3, Mark.OO);
		assertFalse(board.hasLevelDiagonal(Mark.XX));
		assertTrue(board.hasLevelDiagonal(Mark.OO));
		assertTrue(board.hasLevelDiagonalRightLeft(Mark.OO));

	}

	@Test
	public void testisFull() {
		assertFalse(board.isFull());
		for (int x = 0; x < DIM; x++) {
			for (int y = 0; y < DIM; y++) {
				for (int z = 0; z < DIM; z++) {
					board.setField(x, z, y, Mark.OO);

				}
			}
		}
		assertTrue(board.isFull());
	}

	@Test
	public void testDropDown() {
		board.setField(0, 0, Mark.XX);
		assertNotEquals(board.getField(0, 0, 0), Mark.XX);
		assertNotEquals(board.getField(0, 0, 2), Mark.XX);
		assertEquals(board.getField(0, 0, 1), Mark.XX);

	}
}
