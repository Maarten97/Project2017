package controller;

import online.Client;
import online.Protocol;
import view.GameTUI;

public class ClientGame extends Game {
	private Client client;
	private Player clientPlayer;
	private Player opponent;
	public static final String MESSAGE_SEPERATOR = " ";

	public ClientGame(Player s0, Player s1, Client client) {
		super(s0, s1);
		this.client = client;
		this.clientPlayer = s0;
		this.opponent = s1;
	}

	@Override
	public void start() {
		reset();
	}

	public void doPlayerMove() {
		int[] choise = null;
		choise = clientPlayer.determineMove(super.getBoard());
		String x = String.valueOf(choise[0]);
		String y = String.valueOf(choise[1]);
		client.sendMessage(Protocol.CLIENT_SETMOVE + MESSAGE_SEPERATOR + clientPlayer.getName() + 
				MESSAGE_SEPERATOR + x + MESSAGE_SEPERATOR + y);
	}

	public void processTurn(String message) {
		String[] words = message.split(MESSAGE_SEPERATOR);
		int x = -1;
		int z = -1;
		try {
			x = Integer.parseInt(words[2]);
			z = Integer.parseInt(words[3]);
		} catch (NumberFormatException e) {
			GameTUI.printError("Server failt");
			//TODO Disconnect!
		}
		if (words[1].equalsIgnoreCase(clientPlayer.getName())) {
			clientPlayer.placeTile(x, z, clientPlayer.getMark(), super.getBoard());
		} else {
			opponent.placeTile(x, z, opponent.getMark(), super.getBoard());
		}

	}

	public void gameOverWinner(String winner) {
		GameTUI.printMessage("Game is over, player " + winner + "has won!");
		client.gameOverDraw();
		
		
	}



}
