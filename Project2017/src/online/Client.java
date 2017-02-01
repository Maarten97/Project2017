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
import view.GameTUI;

public class Client extends Thread {

	private BufferedReader in;
	private BufferedWriter out;
	private Player clientPlayer;
	private Player opponentPlayer;
	private InetAddress host;
	private int port = 0;
	private Socket socket;
	private Game game;
	private ClientGame clientGame;
	private static final String MESSAGE_SEPERATOR = " ";


	/**
	 * Creates a new Client.
	 * @param args No arguments are given.
	 */
	public static void main(String[] args) {
		new Client();

	}
	
	/**
	 * User is asked if he/she wants to play online or offline. 
	 */
	public Client() {
		GameTUI.printMessage("Welcome by Connect Four 3D!");
		String gameMode = GameTUI.readString("Do you want to play online? (Y/N)");
		if (!gameMode.toLowerCase().startsWith("y")) {

			setupOfflineGame();
		} else {
			setupClient();
		}
	}
	/**
	 * If the player wants to play offline, this method is used to create two players and 
	 * start an offline game.
	 */
	public void setupOfflineGame() {
		GameTUI.printMessage("\nPlayer 1, please answer the next questions:");
		setClientPlayer(createPlayer(Mark.XX));
		GameTUI.printMessage("\nPlayer 2, please answer the next questions:");
		opponentPlayer = createPlayer(Mark.OO);
		game = new Game(getClientPlayer(), opponentPlayer);
		game.start();
	}

	/**
	 * If the player wants to play online, this method is used to make a connection whit a server. 
	 * It will ask for input on Server's IP and port. Then a Socket is created and the 
	 * Thread is started.
	 */
	public void setupClient() {
		try {
			this.host = InetAddress.getByName(GameTUI.readString("What is the Server's IP "
														+ "you want to connect to?"));
		} catch (UnknownHostException e) {
			GameTUI.printError("That is not a valid IP-Adres");
			setupClient();
		}
		try {
			String inputPort = GameTUI.readString("\nWhat is the Server's port? " + 
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
			GameTUI.printMessage("Trying to start a connection");
		} catch (IOException e) {
			GameTUI.printError("\nUnfortunatly, no Socket could be created.");
			setupClient();
		}
		try {
			in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		} catch (IOException e) {
			GameTUI.printError("Something went wrong");
			setupClient();
		}
		this.start();
		this.createGame();
		

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
		

	/** 
	 * CreateGame() will create a player for this client and send a joinrequest to 
	 * the connected server.
	 */
	public void createGame() {
		setClientPlayer(createPlayer(Mark.XX));
		String playerName = getClientPlayerName().toLowerCase();
		this.sendMessage(Protocol.CLIENT_JOINREQUEST + MESSAGE_SEPERATOR + playerName 
													+ MESSAGE_SEPERATOR + "0 0 0 0");
	}
	
	/**
	 * The clientPlayer is created for an Game.
	 * @param mark The Mark that this player will be, for the online Client this is always Mark.XX;
	 * @return the created Player.
	 */
	public Player createPlayer(Mark mark) {
		String playerType = GameTUI.readString("Are you a human? (Y/N)");
		if (!playerType.toLowerCase().equals("y") && !playerType.toLowerCase().equals("n")) {
			GameTUI.printError("Please enter a 'y' or a 'n'");
			createPlayer(mark);
		}

		String playerName = GameTUI.readString("What is your name?");
		if (playerName.contains(" ")) {
			GameTUI.printError("Please do not use a space in your name.");
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
	 * Reads all the messages send by the ClientHandlers from the Server. Each message will 
	 * invoke the right method.
	 * @param answer The message the ClientHandler sended.
	 */
	private void readServerResponse(String answer) {
		String[] replyList = answer.split(MESSAGE_SEPERATOR);
		while (replyList != null) {
			switch (replyList[0]) {
			// Lobbypart
				case Protocol.SERVER_ACCEPTREQUEST:
					this.serverAcceptRequest();
					break;
				case Protocol.SERVER_DENYREQUEST:
					GameTUI.printError("The name '" + replyList[1] + "' is not allowed." + 
														"Please choose an other one.");
					this.createGame();
					break;
				case Protocol.SERVER_WAITFORCLIENT:
					GameTUI.printMessage("Wait until another player joins!");
					break;
				case Protocol.SERVER_STARTGAME:
					startServerGame(replyList[1], replyList[2]);
					break;

				// GamePart
				case Protocol.SERVER_MOVEREQUEST:
					GameTUI.printMessage("It is your turn to make a move");
					clientGame.doPlayerMove();
					break;
				case Protocol.SERVER_DENYMOVE:
					GameTUI.printError("That move was not valid");
					clientGame.doPlayerMove();
					break;
				case Protocol.SERVER_NOTIFYMOVE:
					clientGame.processTurn(answer);
					break;
				case Protocol.SERVER_GAMEOVER:
					if (replyList[1] != null) {
						clientGame.gameOverWinner(replyList[1]);
					} else {
						gameOverDraw();
					}
					break;
				
				//Errors from Server	
				case Protocol.SERVER_CONNECTIONLOST:
					GameTUI.printMessage(replyList[1] + "has left.");
					gameOverDraw();
					break;
				//TODO what to do now?	
				case Protocol.SERVER_INVALIDCOMMAND:
					GameTUI.printError("That last command was not valid.");
					break;
				default:
					GameTUI.printError(answer);
					
					
			}
		}

		
	}

	/** 
	 * Answer to message "acceptrequest" from the Server. It lets the player know that
	 * the client has joined. The player can enter start when it wants to start a game.
	 */
	public void serverAcceptRequest() {
		GameTUI.printMessage("Client has joined the server");
		String start = GameTUI.readString("Enter 'start' if you want to start the game");
		if (!start.contains("start")) {
			serverAcceptRequest();
		}
		this.sendMessage(Protocol.CLIENT_GAMEREQUEST);
	}
	
	/**
	 * if the Server starts a game, a message is send to the clients. This method creates 
	 * a clientGame and initializes a opponentPlayer.
	 * @param reply1 The name of player1.
	 * @param reply2 The name of player2.
	 */
	//@ requires clientPlayer.hasMark() == Mark.XX;
	//@ ensures opponentPlayer.hasMark() == Mark.OO;
	public void startServerGame(String reply1, String reply2) {
		GameTUI.printMessage("A game is being created for clients " + reply1 + "and" + reply2);
		if (clientPlayer.getName().equals(reply1)) {
			opponentPlayer = new ServerPlayer(reply2, Mark.OO);
		} else {
			opponentPlayer = new ServerPlayer(reply1, Mark.OO);
		}
		clientGame = new ClientGame(clientPlayer, opponentPlayer, this);
		clientGame.start();
	}
	
	/**
	 * If an onlineGame is over, there will be asked if the player wants to play
	 * a new game on the same Server. If he does not want to, the client will be
	 * terminated.
	 */
	public void gameOverDraw() {
		String input = GameTUI.readString("\n> Play another time? Yes/No");
		if (input.toLowerCase().startsWith("y")) {
			createGame();
		} else {
			GameTUI.printMessage("Thanks for playing. See you next time!");
			System.exit(0);
		}
		
	}
	

	/** 
	 * Send a message to a ClientHandler. 
	 */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			GameTUI.printError("Connection lost");
		}

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
