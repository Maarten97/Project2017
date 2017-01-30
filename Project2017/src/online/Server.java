package online;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.List;
import java.util.ArrayList;

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

		try {
			String inputPort = readString("\nWhat is the Server's port? " 
										+ "\n(Leave blank for standard port)");
			if (inputPort.equals("")) {
				port = Protocol.PORTNUMBER;
			} else {
				port = Integer.parseInt(inputPort);
			}
			print("\nStarting Server + \nIP Server: " + this.getIP());
			this.start();
		} catch (NumberFormatException e) {
			printError("ERROR: not a valid portnummer!");
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
				print("Client number " + i + " connected");
				ClientHandler handler = new ClientHandler(this, sock);
				handler.start();
				addHandler(handler);
			}
		} catch (IOException e) {
			printError("ERROR: could not create a socket on port " + port);
			start();
		}

	}
	
	/** 
	 * This method processes all the incoming messages from the clientHandlers to this Server.
	 * @param input The message that was sended to the server
	 * @param clientHandler The clientHandler that sended the message.
	 */
	//TODO Synchronized?
	public /* synchronized */ void sendedMessage(String input, ClientHandler clientHandler) {
		String[] words = input.split(MESSAGE_SEPERATOR);
		switch (words[0]) {
		// Lobby
			case Protocol.CLIENT_JOINREQUEST:
				if (!lobby.contains(words[1])) {
					clientHandler.setUserName(words[1]);
					lobby.add(clientHandler);
					clientHandler.sendMessage(Protocol.SERVER_ACCEPTREQUEST + MESSAGE_SEPERATOR + words[1]
							+ MESSAGE_SEPERATOR + words[2] + MESSAGE_SEPERATOR + words[3] + MESSAGE_SEPERATOR + words[4]
							+ MESSAGE_SEPERATOR + words[5]);
				} else {
					clientHandler.sendMessage(Protocol.SERVER_DENYREQUEST + MESSAGE_SEPERATOR + words[1]);
				}
				break;
			case Protocol.CLIENT_GAMEREQUEST:
				if (!playGame.contains(clientHandler)) {
					playGame.add(clientHandler);
				}
				if (playGame.size() == 2) {
					startServerGame();
				}
				break;
	
			// Game
			case Protocol.CLIENT_SETMOVE:
				break;
		}
	}


	//@ ensures playGame.size == 2;
	private void startServerGame() {
		this.broadcast(Protocol.SERVER_STARTGAME, playGame);
		//TODO now we should start a game
		System.err.println("Do not expect to see this.");
		
		
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
	 * Remove a client to the list with connected clientHandlers.
	 * 
	 * @param handler
	 *            the ClientHandler to remove.
	 */
	public void removeHandler(ClientHandler handler) {
		if (clients.contains(handler)) {
			clients.remove(handler);
		}
	}

	public void closeServer() {
		for (ClientHandler client : clients) {
			client.close();
		}
		try {
			serverSock.close();
		} catch (IOException e) {
			printError(e.getMessage());
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

	public void print(String string) {
		System.out.println(string);

	}

	public void printError(String string) {
		System.err.println(string);
	}



}
