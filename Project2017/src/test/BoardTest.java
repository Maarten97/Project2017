package test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;

import exception.FieldNotExsistException;
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

	@Before
	// TODO kan ik ook tiles op board leggen zonder de methode setTiles() te
	// gebruiken?
	public void setUp() throws Exception {
		board = new Board();
		board.setField(0, 0, Mark.BLUE);
		board.setField(0, 1, Mark.BLUE);
		board.setField(1, 1, Mark.BLUE);
		board.setField(2, 1, Mark.BLUE);
		board.setField(1, 0, Mark.RED);
		board.setField(1, 2, Mark.RED);
		board.setField(2, 2, Mark.RED);
		board.setField(0, 3, Mark.RED);
	}



	@Test
	public void deepCopyTest() {
		//TODO implement boardprint
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
		assertEquals(board.getField(0, 0, 0), Mark.BLUE);
		assertEquals(board.getField(0, 1, 0), Mark.BLUE);
		assertEquals(board.getField(1, 2, 0), Mark.RED);
		assertEquals(board.getField(3, 0, 1), Mark.EMPTY);
		assertNotEquals(board.getField(0, 3, 0), Mark.BLUE);
		assertNotEquals(board.getField(3, 3, 1), Mark.BLUE);
	}
	//TODO check if exception has been thrown if field does not exists.
	
//	@Rule
//	public ExpectedException exception = FieldNotExsistException.none();
//	
//	@Test
//	public void testIsEmptyField() throws FieldNotExsistException{
//		assertTrue(board.isEmptyField(3, 3, 3));
//		assertTrue(board.isEmptyField(3, 3, 0));
//		assertFalse(board.isEmptyField(2, 1, 0));
//		exception.expect(FieldNotExsistException.class);
//	
//	}
	@Test
	public void testHasRow(){
		
	}
}
