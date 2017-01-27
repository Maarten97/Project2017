package online;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

import controller.*;
import model.*;

public class Client extends Thread {

	private BufferedReader in;
	private BufferedWriter out;
	private Player clientPlayer;
	private InetAddress host = null;
	private int port = 0;
	private Socket socket;
	private Player opponentPlayer;

	public Client() {
		startClient();
	}
	
	public static void main(String[] args) {
		new Client();
	}

	public void startClient() {
		print("Welcome by Connect Four 3D!");
		String gameMode = readString("Do you want to play online? (Y/N)");
		if (!gameMode.toLowerCase().startsWith("y")) {
			setupOfflineGame();
		} else {
			setupClient();
		}
	}
		
	public void setupOfflineGame() {
		print("\nPlayer 1, please answer the next questions:");
		clientPlayer = createPlayer(Mark.RED);
		print("\nPlayer 2, please answer the next questions:");
		opponentPlayer = createPlayer(Mark.BLUE);
		Game game = new Game(clientPlayer, opponentPlayer);
		game.start();
	}

	public void setupClient() {
		clientPlayer = createPlayer(Mark.RED);
		try {
			this.host = InetAddress.getByName(readString("What is the Server's IP "
														+ "you want to connect to?"));
			//TODO import Validator as Jar (Monday). InetAddressValidator.getInstance().isValid(host);
		} catch (UnknownHostException e) {
			printError("That is not a valid IP-Adres");
			setupClient();
		}
		try {
			String inputPort = readString("\nWhat is the Server's port? " + 
										"\n(leave blank for standard port)");
			if (inputPort.equals("")) {
				port = Protocol.PORTNUMBER;
			} else {
				port = Integer.parseInt(inputPort);
			}
		} catch (NumberFormatException e) {
			System.err.println("ERROR: not a valid portnummer!");
			setupClient();
		}

		try {
			socket = new Socket(host, port);
		} catch (IOException e) {
			printError("\nUnfortunatly, no Socket could be created.");
			setupClient();
		}
		try {
			in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		} catch (IOException e) {
			printError("Something went wrong");
			setupClient();
		}
		//TODO now connecting to server?

	}
	
	public Player createPlayer(Mark mark) {
		String playerType = readString("Are you a human? (Y/N)");
		if (!playerType.toLowerCase().equals("y") && !playerType.toLowerCase().equals("n")) {
			printError("Please enter a 'y' or a 'n'");
			createPlayer(mark);
		}

		String playerName = readString("What is your name?");
		if (playerName.contains(" ")) {
			printError("Please do not use a space in your name.");
			createPlayer(mark);
		}
		if (playerType.toLowerCase().equals("y")) {
			Player player = new HumanPlayer(playerName, mark);
			return player;
		} else {
			Player player = new ComputerPlayer(playerName, mark);
			return player;
		}
	}

	/**
	 * Reads the messages in the socket connection. It opens the inputstream and
	 * will continuously be checked.
	 */
	// TODO make a shutdown method?
	public void run() {
		try {
			String text = in.readLine();
			while (text != null) {
				if (!(text == null) && !text.equalsIgnoreCase("exit")) {
					print(text);
				} else if (text.equalsIgnoreCase("exit")) {
					System.exit(0);
				}
				text = in.readLine();
			}
		} catch (IOException e) {
			// TODO handle exception, nullpointer if no tekst was entered?
		}
		// here a shutdown?
	}

	/** send a message to a ClientHandler. */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			System.err.println("Connection lost");
		}

	}

	public void print(String text) {
		System.out.println(text);

	}

	public void printError(String text) {
		System.err.println(text);

	}

	public static String readString(String tekst) {
		System.out.print(tekst + " ");
		String antw = null;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			antw = in.readLine();
		} catch (IOException e) {
		}
		System.out.println(antw);
		return (antw == null) ? "" : antw;
	}

}
