package it.unive.lisa.analysis.nonrelational.value;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.nonrelational.NonRelationalDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;

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
		extends NonRelationalDomain<T, ValueExpression, ValueEnvironment<T>> {

	@Override
	public default ValueEnvironment<T> assume(ValueEnvironment<T> environment, ValueExpression expression, ProgramPoint pp) throws SemanticException {
		return environment;
	}

	@Override
	@SuppressWarnings("unchecked")
	public default T glb(T other) throws SemanticException {
		if (other == null || this.isBottom() || other.isTop() || this == other || this.equals(other)
				|| this.lessOrEqual(other))
			return (T) this;

		if (other.isBottom() || this.isTop() || other.lessOrEqual((T) this))
			return (T) other;

		return glbAux(other);
	}

	public default T glbAux(T other) {
		return bottom();
	}
}
