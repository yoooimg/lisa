
package it.unive.lisa.analysis.nonrelational.value;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.nonrelational.NonRelationalDomain;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.program.cfg.ProgramPoint;
import org.apache.commons.lang3.tuple.Pair;

/**
 * A non-relational value domain, that is able to compute the value of a
 * {@link ValueExpression} by knowing the values of all program variables.
 * Instances of this class can be wrapped inside an {@link ValueEnvironment} to
 * represent abstract values of individual {@link Identifier}s.
 *
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 *
 * @param <T> the concrete type of the domain
 */
public interface NonRelationalValueDomain<T extends NonRelationalValueDomain<T>>
		extends
		NonRelationalDomain<T, ValueExpression, ValueEnvironment<T>> {

//	@Override
//	Pair<ValueEnvironment<T>, ValueEnvironment<T>> split(
//			ValueEnvironment<T> environment,
//			ValueExpression expr,
//			ProgramPoint src,
//			ProgramPoint dest,
//			SemanticOracle oracle) throws SemanticException;
}
