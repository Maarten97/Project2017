package online;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;

	public ClientHandler(Server serverArg, Socket socketArg) throws IOException {
		server = serverArg;
		sock = socketArg;
		System.out.println("Handler created!");
		in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
	}
	
	

}
