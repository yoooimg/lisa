package it.unive.lisa.program.cfg.statement.call.resolution;

import it.unive.lisa.program.cfg.Parameter;
import it.unive.lisa.program.cfg.statement.Expression;

/**
 * A strategy for matching call signatures. Depending on the language, targets
 * of calls might be resolved (at compile time or runtime) relying on the static
 * or runtime type of their parameters. Some languages might also have named
 * parameter passing, allowing shuffling of parameters. Each strategy comes with
 * a different {@link #matches(Parameter[], Expression[])} implementation that
 * can automatically detect if the signature of a cfg is matched by the given
 * expressions representing the parameters for a call to that cfg.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public interface ResolutionStrategy {

	/**
	 * Yields {@code true} if and only if the parameter list of a cfg is matched
	 * by the given actual parameters, according to this strategy.
	 * 
	 * @param formals the parameters definition of the cfg
	 * @param actuals the expression that are used as call parameters
	 * 
	 * @return {@code true} if and only if that condition holds
	 */
	boolean matches(Parameter[] formals, Expression[] actuals);
}
