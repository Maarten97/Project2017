package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import controller.*;
import model.*;

public class GameTUI {
	
	//TODO Implement.
	
	public GameTUI() {

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
	
    public void printResult(Board board) {
//        if () {
//            Player winner = board.isWinner(players[0].getMark()) ? players[0]
//                    : players[1];
//            System.out.println("Speler " + winner.getName() + " ("
//                    + winner.getMark().toString() + ") has won!");
//        } else {
//            System.out.println("Draw. There is no winner!");
//        }
    }

}
