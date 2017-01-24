package controller;

import model.Board;
import model.Mark;

/**
 * Interface for computer strategy. Project module 2
 * 
 * @author Maarten Looijenga and Thomas Hogema
 */
public interface Strategy {

	public String getName();
	public int determineMove(Board b, Mark m);
}
