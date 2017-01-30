package controller;

import java.util.Scanner;

import model.Board;
import model.Mark;

/**
 * Class for a human player. Project module 2
 * 
 * @author Maarten Looijenga and Thomas Hogema
 */
public class HumanPlayer extends Player {

	// -- Constructors -----------------------------------------------

	/*
	 * @ requires name != null; requires mark == Mark.RED || mark == Mark.BLUE;
	 * ensures this.getName() == name; ensures this.getMark() == mark;
	 */
	/**
	 * Creates a new human player object.
	 * 
	 * @param name Name of the created player
	 * @param mark Mark of the created player
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
	 * @param board the game board
	 * @return the player's chosen field
	 */
	public int[] determineMove(Board board) {
		
		boolean needsInput = true;
		int choiceX = -1;
		int choiceZ = -1;
		
		while (needsInput) {
			String promptX = "> " + getName() + " (" + getMark().toString() + ")" + ", "
					+ "What row do you want to place your tile?";
			choiceX = readInt(promptX);

			String promptZ = "> " + getName() + " (" + getMark().toString() + ")" + ", "
					+ "What column do you want to place your tile?";
			choiceZ = readInt(promptZ);

			needsInput = !board.validMove(choiceX, choiceZ);
			
			if (needsInput == true) {
				System.out.println("Coordinate: (" + choiceX + "," + choiceZ + ") "
					+ "is not a valid choice. Please provide another coordinate");
			}
			
		}
		return new int[]{choiceX, choiceZ};
	}
	
	// TODO check if valid in controller!
	/*while (!valid) {
		System.out.println("ERROR:  " + choice + " is no valid choice.");
		choice = readInt(prompt);
		valid = board.isField(choice) && board.isEmptyField(choice);
	}
	return choice; 
	*/

	/**
	 * Writes a prompt to standard out and tries to read an int value from
	 * standard in. This is repeated until an int value is entered.
	 * 
	 * @param prompt the question to prompt the user
	 * @return the first int value which is entered by the user
	 */
	private int readInt(String prompt) {
		int value = 0;
		boolean intRead = false;
		@SuppressWarnings("resource")
		Scanner line = new Scanner(System.in);
		do {
			System.out.print(prompt);
			try (Scanner scannerLine = new Scanner(line.nextLine())) {
				if (scannerLine.hasNextInt()) {
					intRead = true;
					value = scannerLine.nextInt();
				}
			}
		} while (!intRead);
		return value;
	}

}
