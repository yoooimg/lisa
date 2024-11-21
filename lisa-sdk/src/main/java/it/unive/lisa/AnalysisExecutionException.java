package it.unive.lisa;

/**
 * A generic {@link AnalysisException} that indicates that something has gone
 * wrong during the analysis. Instances of this exception will be catched at the
 * root of the analysis execution.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class AnalysisExecutionException extends AnalysisException {

	private static final long serialVersionUID = 3947756263710715139L;

	/**
	 * Builds the exception.
	 */
	public AnalysisExecutionException() {
		super();
	}

	/**
	 * Builds the exception.
	 * 
	 * @param message the message of this exception
	 * @param cause   the cause of this exception
	 */
	public AnalysisExecutionException(
			String message,
			Throwable cause) {
		super(message, cause);
	}

	/**
	 * Builds the exception.
	 * 
	 * @param message the message of this exception
	 */
	public AnalysisExecutionException(
			String message) {
		super(message);
	}

	/**
	 * Builds the exception.
	 * 
	 * @param cause the cause of this exception
	 */
	public AnalysisExecutionException(
			Throwable cause) {
		super(cause);
	}
}
