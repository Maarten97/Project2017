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
	private static final String MESSAGE_SEPERATOR = " ";
	
	public static void main(String[] args) {
		Client client = new Client();
		//eerst startup en socket connection maken.
		client.start();
		client.createGame();
	}

	public Client() {
		print("Welcome by Connect Four 3D!");
		String gameMode = readString("Do you want to play online? (Y/N)");
		if (!gameMode.toLowerCase().startsWith("y")) {
			setupOfflineGame();
		} else {
			setupClient();
		}
	}
	
	/**
	 * Reads the messages in the socket connection. It opens the inputstream and
	 * will continuously be checked.
	 */

	public void run() {
		boolean running = true;
		try {
			while (running) {

				while (in.ready()) {
					readServerResponse(in.readLine());
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			try {
				in.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
	}
		
	public void setupOfflineGame() {
		print("\nPlayer 1, please answer the next questions:");
		setClientPlayer(createPlayer(Mark.RED));
		print("\nPlayer 2, please answer the next questions:");
		opponentPlayer = createPlayer(Mark.BLUE);
		Game game = new Game(getClientPlayer(), opponentPlayer);
		game.start();
	}

	public void setupClient() {
//		clientPlayer = createPlayer(Mark.RED);
		try {
			this.host = InetAddress.getByName(readString("What is the Server's IP "
														+ "you want to connect to?"));
			//TODO import Validator as Jar (Monday). 
			//InetAddressValidator.getInstance().isValid(host);
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
		

	}
	
	public void createGame() {
		setClientPlayer(createPlayer(Mark.RED));
		String playerName = getClientPlayerName().toLowerCase();
		this.sendMessage(Protocol.CLIENT_JOINREQUEST + MESSAGE_SEPERATOR + playerName 
													+ MESSAGE_SEPERATOR + "0 0 0 0");
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


	
	private void readServerResponse(String answer) {
		// Server_InvalidCommand and Server_ConnectionLost not yet implemented.

		String[] replyList = answer.split(MESSAGE_SEPERATOR);
		while (replyList != null) {
			switch (replyList[0]) {
			// Lobbypart
				case Protocol.SERVER_ACCEPTREQUEST:
					this.serverAcceptRequest();
					break;
				case Protocol.SERVER_DENYREQUEST:
					printError("The name '" + replyList[1] + "' is not allowed." + 
														"Please choose an other one.");
					this.createGame();
					break;
				case Protocol.SERVER_WAITFORCLIENT:
					print("Wait until another player joins!");
					break;
				case Protocol.SERVER_STARTGAME:
					print("A game is being created for clients " + replyList[1] + 
															"and" + replyList[2]);
					break;

				// GamePart
				case Protocol.SERVER_MOVEREQUEST:
					print("It is your turn to make a move");
					// doMove
					break;
				case Protocol.SERVER_DENYMOVE:
					printError("That move was not valid");
					break;
				case Protocol.SERVER_NOTIFYMOVE:
					// TODO implement
					break;
				case Protocol.SERVER_GAMEOVER:
					print("Player " + replyList[1] + "has won the game!");
					break;
				default:
					print(answer);
					
			}
		}

		
	}
	
	public void serverAcceptRequest() {
		print("Client has joined the server");
		String start = readString("Enter 'start' if you want to start the game");
		if (!start.contains("start")) {
			serverAcceptRequest();
		}
		this.sendMessage(Protocol.CLIENT_GAMEREQUEST);
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
	//TODO should have a Thread for itself?
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

	public String getClientPlayerName() {
		return getClientPlayer().getName();
	}

	public Player getClientPlayer() {
		return clientPlayer;
	}

	public void setClientPlayer(Player clientPlayer) {
		this.clientPlayer = clientPlayer;
	}
	


}
