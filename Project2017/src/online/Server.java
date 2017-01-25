package online;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;

import ss.week7.cmdchat.ClientHandler;

public class Server {
	
	private int port = 1337;
	public String localhost;
	
	public static void main(String[] args) {
		new Server();
	}

	public Server() {

		
		try {
			String inputPort = readString("Please enter serverport, "
					+ "leave empty for standard port:");
			if (!inputPort.equals("")) {
				port = Integer.parseInt(inputPort);
			}

			System.out.println("Starting server");
			this.start();

		} catch (NumberFormatException e) {
			System.err.println("Portnumber in not a valid number, please try again");
			new Server();
		}

	}
	
	private void start() {
        try {
            ServerSocket serverSock = new ServerSocket(port);
            int i = 0;
            while (true) {
            	Socket sock = serverSock.accept();
            	System.out.println("Client number " + (i++) + "connected");
            	ClientHandler handler = new ClientHandler(this, sock);
            	handler.start();
            	addHandler(handler);
            }
        } catch (IOException e) {
            System.out.println("ERROR: could not create a socket on port " + port);
            new Server();
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
	

}
