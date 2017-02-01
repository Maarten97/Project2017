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
		update();
	}

	public void doPlayerMove() {
		update();
		int[] choise = null;
		choise = clientPlayer.determineMove(super.getBoard());
		int x = choise[1];
		int z = choise[0];
		System.out.println("x: " + x + " z: " + z);
		client.sendMessage(Protocol.CLIENT_SETMOVE + MESSAGE_SEPERATOR + clientPlayer.getName() + 
				MESSAGE_SEPERATOR + x + MESSAGE_SEPERATOR + z);
	}

	public void processTurn(String message) {
		System.out.println("Procossing turn.");
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
			clientPlayer.placeTile(z, x, clientPlayer.getMark(), super.getBoard());
		} else {
			opponent.placeTile(z, x, opponent.getMark(), super.getBoard());
		}

	}

	public void gameOverWinner(String winner) {
		GameTUI.printMessage("Game is over, player " + winner + "has won!");
		client.gameOverDraw();
		
		
	}



}
