package test;

import model.Mark;
import view.GameTUI;
import controller.HumanPlayer;
import model.Board;


public class GameTUITest {

	public GameTUITest() {
		// TODO Auto-generated constructor stub
	}

	public static void main(String[] args) {

		String a = GameTUI.readString("typ hier wat leuks: ");
		System.out.println("je typte: " + a);
		
		int i = GameTUI.readInt("Typ je int: ");
		System.out.println("je typte: " + i);
		
		HumanPlayer henk = new HumanPlayer("Henk", Mark.RED);
		henk.determineMove(new Board());
	}

}
