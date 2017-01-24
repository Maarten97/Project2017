package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import controller.*;
import model.*;

public class GameTUI {
	private Game game;
	
	//TODO Implement.
	
	public GameTUI(Game game) {
		this.game = game;
	}
	
	//TODO has to be implemented!
	@Override
	public String toString() {
		return "Board should print here";
	}
	
	public static String readString(String tekst) {
		System.out.print(tekst);
		String antw = null;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(
					System.in));
			antw = in.readLine();
		} catch (IOException e) {
		}

		return (antw == null) ? "" : antw;
	}
	
	public void printResult(Player player) {
		System.out.println("Speler " + player.getName() + " (" + 
				player.getMark().toString() + ") has won!");

	}

	public static void printDraw() {
		System.out.println("Draw. There is no winner!");
		
	}

}
