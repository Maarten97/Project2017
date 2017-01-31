package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import controller.*;
import model.*;

public class GameTUI {
	private Game game;

	// TODO Implement.

	public GameTUI(Game game) {
		this.game = game;
	}

	/**
	 * Returns a visual representation of the board using Board.toString().
	 * 
	 * @return a print of all 4 board levels.
	 */
	public String printBoard() {
		return game.getBoard().toString();

	}

	/**
	 * Reat a string from the standard input.
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
	 * Read a string from the standard input and convert it to an int.
	 * 
	 * @param tekst text that should be printed before looking for input.
	 * @return given int, and -1 if invalid input.
	 */
	public static int readInt(String tekst) {
		System.out.print(tekst);
		int parsed = -1;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			parsed = Integer.parseInt(in.readLine());

		} catch (IOException e) {
		} catch (NumberFormatException e) {
			//als geen geldige int (dus waarschijnlijke 
			return -12845;
		}

		return parsed;
	}
	
	
	public void printMessage(String text) {
		System.out.println(text);
	}

	public void printError(String text) {
		System.err.println(text);
	}
	
	public void printResult(Player player) {
		System.out.println("Speler " + player.getName() + 
				" (" + player.getMark().toString() + ") has won!");

	}

	public static void printDraw() {
		System.out.println("Draw. There is no winner!");

	}

}
