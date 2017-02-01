package controller;

import model.Board;
import model.Mark;
import view.GameTUI;

/**
 * Class for a human player. Project module 2
 * 
 * @author Maarten Looijenga and Thomas Hogema
 */
public class HumanPlayer extends Player {

	// -- Constructors -----------------------------------------------

	/**
	 * Creates a new human player object.
	 * 
	 * @param name Name of the created player
	 * @param mark Mark of the created player
	 */
	/*
	 * @ requires name != null; requires mark == Mark.RED || mark == Mark.BLUE;
	 * @ ensures this.getName() == name; ensures this.getMark() == mark;
	 */
	public HumanPlayer(String name, Mark mark) {
		super(name, mark);
	}

	// -- Commands ---------------------------------------------------

	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the standard input/output. The user can also ask for a hint.
	 * 
	 * @param board the game board
	 * @return the player's chosen field
	 */
	/*
	 * @ requires board != null; ensures board.isField(\result) &&
	 * board.isEmptyField(\result);
	 */
	public int[] determineMove(Board board) {
		boolean needsInput = true;
		int choiceX = -1;
		int choiceZ = -1;
		
		while (needsInput) {
			String answer = GameTUI.readString("\n Tip: if you're stuck, type 'hint' to get a "
					+ "suggestion for a move \n > " + getName() + " (" + getMark().toString() + ")" 
					+ ", What row do you want to place your tile? ");
			
			if (answer.toLowerCase().equals("hint")) {
				int[] sug = CommonStrategyUtils.getRandomFreeField(board);
				GameTUI.printMessage("A possible move is column " + sug[1] + " and row " + sug[0]);
				
				choiceX = GameTUI.readInt("> " + getName() + " (" + getMark().toString() + ")" + 
						", " + "What column do you want to place your tile? ");
			} else {
				try {
					choiceX = Integer.parseInt(answer);
				} catch (NumberFormatException e) {
					GameTUI.printMessage("Please provide an integer as input");
					continue;
				}
			}
			
			choiceZ = GameTUI.readInt("> " + getName() + " (" + getMark().toString() + ")" + ", "
					+ "What row do you want to place your tile? ");

			needsInput = !board.validMove(choiceX, choiceZ);

			if (needsInput == true) {
				if (choiceX == -12845 || choiceZ == -12845) {
					System.out.println("This is not a valid input. Please provide two "
							+ "integers for the coordinates");
				} else {
					System.out.println("Coordinate: (" + choiceX + "," + choiceZ + ") "
							+ "is not a valid choice. Please provide another coordinate");
				}
			}
		}
		return new int[] {choiceX, choiceZ};
	}


}
