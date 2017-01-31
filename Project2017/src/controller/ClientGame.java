package controller;

import online.Client;

public class ClientGame extends Game {
	private Client client;
	private Player clientPlayer;
	private ServerPlayer opponent;

	public ClientGame(Player s0, ServerPlayer s1, Client client) {
		super(s0, s1);
		this.client = client;
		this.clientPlayer = s0;
		this.opponent = s1;
	}

	@Override
	public void start() {
		reset();
	}
	
	
}
