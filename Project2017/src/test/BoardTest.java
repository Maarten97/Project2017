package test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import model.Board;
import model.Mark;
/**
 * Provides a JUnit test file for the class board.
 * Testclass yields if board.DIM == 4.
 * @author Maarten Looijenga
 *
 */
public class BoardTest {
	private Board board;
	

	@Before
	// TODO kan ik ook tiles op board leggen zonder de methode setTiles() te
	// gebruiken?
	public void setUp() throws Exception {
		board = new Board();
	}

	//TODO need to test the length of the field list?
	
	
	@Test
	//TODO implement
	public void deepCopyTest() {
//		assertEquals(board, board.deepCopy());
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
		assertTrue(board.isField(0));
		assertTrue(board.isField(63));
		assertTrue(board.isField(26));
		assertFalse(board.isField(-1));
		assertFalse(board.isField(64));
		assertFalse(board.isField(100));
		
	}
	
	@Test
	public void testIsFieldCoords() {
		assertTrue(board.isField(0, 0, 0));
		assertTrue(board.isField(3, 3, 3));
		assertTrue(board.isField(1, 2, 0));
		assertFalse(board.isField(1, 2, 4));
		assertFalse(board.isField(-1, 2, 3));
		assertFalse(board.isField(1, 10, 0));	
	}
	
	@Test
	public void testGetField(){
		
	}

}
