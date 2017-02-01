package online;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

import controller.*;
import model.Mark;

public class ClientHandler extends Thread {

	private Server server;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private String userName;
	private ServerPlayer player;
	private Mark mark;

	public ClientHandler(Server serverArg, Socket socketArg) throws IOException {
		server = serverArg;
		sock = socketArg;
		print("Handler created!");
		in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
	}

	public void close() {
		server.removeHandler(this);

	}

	public void run() {
		try {
			while (true) {
				String input = in.readLine();
				server.sendedMessage(input, this);
			}
		} catch (IOException e) {
			printError("Could not read input");
			print(e.getMessage());
			server.connectionLost(this);
			close();

		}
	}

	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			printError("Message could not be send");
			print(e.getMessage());
			close();
		}

	}

	public void print(String text) {
		System.out.println(text);

	}

	public void printError(String text) {
		System.err.println(text);

	}

	public String getUserName() {
		return userName;
	}

	public void setUserName(String name) {
		this.userName = name;
	}

	public ServerPlayer getPlayer() {
		return player;
	}

	public void setPlayer(ServerPlayer player) {
		this.player = player;
		this.setMark(player.getMark());
	}

	public Mark getMark() {
		return mark;
	}

	public void setMark(Mark mark) {
		this.mark = mark;
	}

}
