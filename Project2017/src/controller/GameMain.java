package controller;

import exception.FieldNotExsistException;
import model.Mark;

public class GameMain {

	public GameMain() {
		
	}
	
	public static void main(String[] args) throws FieldNotExsistException {
		Player player1;
		Player player2;
		player1 = new HumanPlayer("Thomas", Mark.BLUE);
		player2 = new HumanPlayer("Henkie", Mark.RED);
		Game game = new Game(player1, player2);
		game.start();
				
	}

}
