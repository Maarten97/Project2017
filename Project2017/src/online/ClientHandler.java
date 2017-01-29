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
		print("Handler created!");
		in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
	}

	public void close() {
		server.removeHandler(this);
		
	}
	
	public void run(){
		try{
			while(true){
				String input = in.readLine();
				server.sendedMessage(input, this);
			}
		} catch (IOException e){
			printError("Could not read input");
			print(e.getMessage());
			close();
			
		}
	}
	
	public void sendMessage(String message) {
		try{
			out.write(message);
			out.newLine();
			out.flush();
		} catch(IOException e){
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
	

}
