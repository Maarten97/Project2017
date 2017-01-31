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

	/*
	 * @ requires board != null; ensures board.isField(\result) &&
	 * board.isEmptyField(\result);
	 * 
	 */
	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the standard input/output.
	 * 
	 * @param board
	 *            the game board
	 * @return the player's chosen field
	 */
	public int[] determineMove(Board board) {

		boolean needsInput = true;
		int choiceX = -1;
		int choiceZ = -1;

		while (needsInput) {
			choiceZ = GameTUI.readInt("> " + getName() + " (" + getMark().toString() + ")" + ", "
					+ "What column do you want to place your tile? ");

			choiceX = GameTUI.readInt("> " + getName() + " (" + getMark().toString() + ")" + ", "
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
