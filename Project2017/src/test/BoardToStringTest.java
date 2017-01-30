package test;

import java.io.IOException;

import model.Board;
import model.Mark;


public class BoardToStringTest {
	
	
	public static void main(String[] args) throws IOException {
		
		/*System.out.println("\u001B[31m" + "26AB" + "\u001B[0m" );
	    System.out.println ((char)27 + "[2J");*/
	    
		Board b = new Board();
		b.setField(0, 0, Mark.RED);
		b.setField(0, 0, Mark.BLUE);
		
		System.out.println(b.toString());
		System.out.println("hai");
		System.out.println(b.getField(0, 0, 0));
		System.out.println(Mark.RED == b.getField(0, 0, 0));
		System.out.println("test: "  + (false || true || false));
	}
}
