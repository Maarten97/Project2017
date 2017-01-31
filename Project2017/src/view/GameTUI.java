package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import controller.*;

/**
 * TUI for Tic Tac Toe 3D
 * 
 * @author Maarten Looijenga en Thomas Hogema
 *
 */
public class GameTUI {
	
	// -- Instance variables -----------------------------------------
	private Game game;

	// -- Constructors -----------------------------------------------

	/**
	 * Saves the current game in an instance variable.
	 * 
	 * @param game the game to represent.
	 */
	public GameTUI(Game game) {
		this.game = game;
	}

	// -- Queries/Commands ----------------------------------------------------

	/**
	 * Returns a visual representation of the board using Board.toString().
	 * 
	 * @return a print of all 4 board levels.
	 */
	public String printBoard() {
		return "\ncurrent game situation: \n\n" + game.getBoard().toString() + "\n";

	}

	/**
	 * Read a string from the standard input.
	 * 
	 * @param tekst text that should be printed before looking for input.
	 * @return entered String, or "" if null.
	 */
	public static String readString(String tekst) {
		System.out.print(tekst);
		String antw = null;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			antw = in.readLine();
		} catch (IOException e) {
		}

		return (antw == null) ? "" : antw;
	}

	/**
	 * Read a string from the standard input and convert it to an integer.
	 * 
	 * @param tekst text that should be printed before looking for input.
	 * @return given integer, and -12845 if invalid input, which is most likely a String.
	 */
	public static int readInt(String tekst) {
		System.out.print(tekst);
		int parsed = -1;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			parsed = Integer.parseInt(in.readLine());

		} catch (IOException e) {
		} catch (NumberFormatException e) {
			return -12845;
		}
		return parsed;
	}
	
	/**
	 * Print a message to the standard output.
	 * 
	 * @param text Text to be printed
	 */
	public void printMessage(String text) {
		System.out.println(text);
	}

	/**
	 * Print an error to the standard output.
	 * 
	 * @param text Error to be printed
	 */
	public void printError(String text) {
		System.err.println(text);
	}
	
	/**
	 * Print a String telling the provided player has won.
	 * 
	 * @param player Player that has won.
	 */
	public void printWinner(Player player) {
		System.out.println("Speler " + player.getName() + 
				" (" + player.getMark().toString() + ") has won!");

	}

	/**
	 * Print a statement saying there is a draw.
	 */
	public static void printDraw() {
		System.out.println("Draw. There is no winner!");
	}

}
