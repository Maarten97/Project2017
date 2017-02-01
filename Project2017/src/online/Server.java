package online;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Map;
import java.util.ArrayList;
import java.util.HashMap;

import controller.*;
import view.GameTUI;

public class Server {

	private static final String MESSAGE_SEPERATOR = " ";
	private int port = 1337;
	public String localhost;

	/**
	 * All clients connected to the server.
	 */
	private List<ClientHandler> clients;
	private List<ClientHandler> playGame;
	private List<ClientHandler> lobby;
	private ServerSocket serverSock;
	private Map<ServerGame, List<ClientHandler>> gamesPlaying;

	/**
	 * All games that has been started.
	 */
	/* private List<GameServer> gameServers; */

	public static void main(String[] args) {
		new Server();
	}

	public Server() {
		this.clients = new ArrayList<>();
		this.playGame = new ArrayList<>();
		this.lobby = new ArrayList<>();
		gamesPlaying = new HashMap<>();

		
		try {
			String inputPort = GameTUI.readString("\nWhat is the Server's port? " 
										+ "\n(Leave blank for standard port)");
			if (inputPort.equals("")) {
				port = Protocol.PORTNUMBER;
			} else {
				port = Integer.parseInt(inputPort);
			}
			GameTUI.printMessage("\nStarting Server + \nIP Server: " + this.getIP());
			this.start();
		} catch (NumberFormatException e) {
			GameTUI.printError("ERROR: not a valid portnummer!");
			new Server();
		}
	}

	public void start() {
		try {
			serverSock = new ServerSocket(port);
			int i = 0;
			while (true) {
				Socket sock = serverSock.accept();
				i++;
				GameTUI.printMessage("Client number " + i + " connected");
				ClientHandler handler = new ClientHandler(this, sock);
				handler.start();
				addHandler(handler);
			}
		} catch (IOException e) {
			GameTUI.printError("ERROR: could not create a socket on port " + port);
			start();
		}

	}
	
	/** 
	 * This method processes all the incoming messages from the clientHandlers to this Server.
	 * @param input The message that was sended to the server
	 * @param clientHandler The clientHandler that sended the message.
	 */
	public synchronized void sendedMessage(String input, ClientHandler clientHandler) {
		GameTUI.printMessage("Message recieved: " + input);
		String[] words = input.split(MESSAGE_SEPERATOR);
		switch (words[0]) {
		// Lobby
			case Protocol.CLIENT_JOINREQUEST:
				if (!lobby.equals(words[1])) {
					clientHandler.setUserName(words[1]);
					lobby.add(clientHandler);
					clientHandler.sendMessage(Protocol.SERVER_ACCEPTREQUEST + MESSAGE_SEPERATOR +
							words[1] + MESSAGE_SEPERATOR + words[2] + MESSAGE_SEPERATOR + words[3] 
									+ MESSAGE_SEPERATOR + words[4] + MESSAGE_SEPERATOR + words[5]);
				} else {
					clientHandler.sendMessage(Protocol.SERVER_DENYREQUEST
											+ MESSAGE_SEPERATOR + words[1]);
				}
				break;
			case Protocol.CLIENT_GAMEREQUEST:

				if (!playGame.contains(clientHandler)) {
					playGame.add(clientHandler);
				}
				if (playGame.size() == 2) {
					startServerGame();
				}
				if (playGame.size() < 2) {
					clientHandler.sendMessage(Protocol.SERVER_WAITFORCLIENT);
				}
				break;
	
			// Game
			case Protocol.CLIENT_SETMOVE:
				for (ServerGame s : gamesPlaying.keySet()) {
					if (gamesPlaying.get(s).contains(clientHandler)) {
						s.processTurn(input, clientHandler);
					}
				}
				break;
			default:
				clientHandler.sendMessage(Protocol.SERVER_INVALIDCOMMAND 
											+ MESSAGE_SEPERATOR + input);
		}
	}



	//@ ensures playGame.size == 2;
	private void startServerGame() {
		lobby.remove(playGame.get(0));
		lobby.remove(playGame.get(1));
		ServerGame game = new ServerGame(playGame.get(0), playGame.get(1), this);
		gamesPlaying.put(game, playGame);
		playGame.clear();
		game.start();
	}

	/**
	 * Prints the IP address of the Server.
	 * 
	 * @return IP of server
	 */
	public String getIP() {
		try {
			return InetAddress.getLocalHost().toString();
		} catch (UnknownHostException e) {
			e.printStackTrace();
			return "Could not print IP of ServerHost";
		}
	}

	/**
	 * Add a client to the list with connected clientHandlers.
	 * 
	 * @param handler
	 *            the ClientHandler to add.
	 */
	public void addHandler(ClientHandler handler) {
		if (handler != null && clients.contains(handler)) {
			clients.add(handler);
		}

	}

	/**
	 * Remove a client to the list with connected clientHandlers, handlers in the lobby
	 * and handlers that are playing a game.
	 * 
	 * @param handler
	 *            the ClientHandler to remove.
	 */
	public void removeHandler(ClientHandler handler) {
		if (clients.contains(handler)) {
			clients.remove(handler);
			if (lobby.contains(handler)) {
				lobby.remove(handler);
			}
			if (playGame.contains(handler)) {
				playGame.remove(handler);
			}
		}
	}

	public void closeServer() {
		for (ClientHandler client : clients) {
			client.close();
		}
		try {
			serverSock.close();
		} catch (IOException e) {
			GameTUI.printError(e.getMessage());
		}
	}

	/**
	 * Broadcast a message to all different clients.
	 * 
	 * @param message
	 *            A String that will be send to all the clients.
	 */
	public void broadcast(String message, List<ClientHandler> list) {
		if (message != null) {
			for (ClientHandler handler : list) {
				handler.sendMessage(message);
			}
		}
	}

	public void closeGame(List<ClientHandler> players) {
		for (ClientHandler c : players) {
			playGame.remove(c);
			lobby.add(c);
		}
		
	}

	public void connectionLost(ClientHandler clientHandler) {
		String name = clientHandler.getName().toLowerCase();
		removeHandler(clientHandler);
		broadcast(Protocol.SERVER_CONNECTIONLOST + MESSAGE_SEPERATOR + name, clients);
	}




}
