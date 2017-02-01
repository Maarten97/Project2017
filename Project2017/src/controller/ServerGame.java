package controller;

import java.util.ArrayList;
import java.util.List;

import model.Mark;
import online.*;
import view.GameTUI;

public class ServerGame extends Game {

	private int currentPlayerIndex;
	private List<ClientHandler> currentPlayer;
	public static final String MESSAGE_SEPERATOR = " ";
	private Server server;
	private ServerPlayer player1;
	private ServerPlayer player2;

	public ServerGame(ClientHandler c1, ClientHandler c2, Server server) {
		super(c1.getPlayer(), c2.getPlayer());
		this.server = server;
		this.currentPlayer = new ArrayList<>();
		currentPlayer.add(0, c1);
		currentPlayer.add(1, c2);
		String playerName1 = c1.getUserName();
		String playerName2 = c2.getUserName();
		player1 = new ServerPlayer(playerName1, Mark.XX);
		player2 = new ServerPlayer(playerName2, Mark.XX);
		c1.setPlayer(player1);
		c2.setPlayer(player2);
		server.broadcast(Protocol.SERVER_STARTGAME + MESSAGE_SEPERATOR + playerName1 
								+ MESSAGE_SEPERATOR + playerName2, currentPlayer);

		
	}


	
	@Override
	public void start() {
		reset();
		currentPlayerIndex = 0;
		sendTurn();

	}

	public void sendTurn() {
		getCurrentClientHandler().sendMessage(Protocol.SERVER_MOVEREQUEST + MESSAGE_SEPERATOR 
								+ getCurrentClientHandler().getUserName());
	}

	public void processTurn(String input, ClientHandler client) {
		if (currentPlayer.get(currentPlayerIndex).equals(client)) {
			String[] words = input.split(MESSAGE_SEPERATOR);
			int x = -1;
			int z = -1;
			int y = -1;
			try {
				x = Integer.parseInt(words[1]);
				z = Integer.parseInt(words[2]);
			} catch (NumberFormatException e) {
				getCurrentClientHandler().sendMessage(Protocol.SERVER_DENYMOVE);
				GameTUI.printError("Could not compile coordinates to int.");
			}
			if (!super.getBoard().validMove(x, z)) {
				getCurrentClientHandler().sendMessage(Protocol.SERVER_DENYMOVE);
				GameTUI.printError("Move is not valid. x: " + x + "z: " + z);
			} else {
				y = super.getBoard().dropDown(x, z);
				server.broadcast(Protocol.SERVER_NOTIFYMOVE + MESSAGE_SEPERATOR + 
						getCurrentClientHandler().getUserName()	+ MESSAGE_SEPERATOR 
						+ x + MESSAGE_SEPERATOR + z + MESSAGE_SEPERATOR + y, currentPlayer);

				getCurrentClientHandler().getPlayer().placeTile(z, x, 
						getCurrentClientHandler().getMark(), super.getBoard());
				if (super.gameOver()) {
					if (super.hasWinner()) {
						String winnerName = null;
						if (super.getBoard().isWinner(currentPlayer.get(0).getMark())) {
							winnerName = currentPlayer.get(0).getUserName();
						} else {
							winnerName = currentPlayer.get(1).getUserName();
						}
						server.broadcast(Protocol.SERVER_GAMEOVER + MESSAGE_SEPERATOR 
														+ winnerName, currentPlayer);
					} else {
						server.broadcast(Protocol.SERVER_GAMEOVER, currentPlayer);
					}
					server.closeGame(currentPlayer);
				}
				currentPlayerIndex = (currentPlayerIndex + 1) % NUMBER_PLAYERS;
				sendTurn();
			}
		}
	}

	public ClientHandler getCurrentClientHandler() {
		return currentPlayer.get(currentPlayerIndex);
	}
}
