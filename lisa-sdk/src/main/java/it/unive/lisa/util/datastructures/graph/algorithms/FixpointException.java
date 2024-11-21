package it.unive.lisa.util.datastructures.graph.algorithms;

/**
 * An exception raised during the fixpoint computation.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class FixpointException extends Exception {

	private static final long serialVersionUID = 8975446457619020051L;

	/**
	 * Builds the exception.
	 */
	public FixpointException() {
		super();
	}

	/**
	 * Builds the exception.
	 * 
	 * @param message the message associated with this exception
	 * @param cause   the underlying cause of this exception
	 */
	public FixpointException(
			String message,
			Throwable cause) {
		super(message, cause);
	}

	/**
	 * Builds the exception.
	 * 
	 * @param message the message associated with this exception
	 */
	public FixpointException(
			String message) {
		super(message);
	}

	/**
	 * Builds the exception.
	 * 
	 * @param cause the underlying cause of this exception
	 */
	public FixpointException(
			Throwable cause) {
		super(cause);
	}

}
