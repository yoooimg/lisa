package it.unive.lisa.cfg.statement;

import java.util.Objects;

import it.unive.lisa.cfg.CFG;

/**
 * A statement that raises an error, stopping the execution of the current CFG
 * and propagating the error to among the call chain.
 * 
 * @author @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class Throw extends Statement {

	/**
	 * The expression representing the error to raise
	 */
	private final Expression expression;

	/**
	 * Builds the throw, raising {@code expression} as error. The location where
	 * this throw happens is unknown (i.e. no source file/line/column is
	 * available).
	 * 
	 * @param cfg        the cfg that this statement belongs to
	 * @param expression the expression to raise as error
	 */
	public Throw(CFG cfg, Expression expression) {
		this(cfg, null, -1, -1, expression);
	}

	/**
	 * Builds the throw, raising {@code expression} as error, happening at the given
	 * location in the program.
	 * 
	 * @param cfg        the cfg that this statement belongs to
	 * @param sourceFile the source file where this statement happens. If unknown,
	 *                   use {@code null}
	 * @param line       the line number where this statement happens in the source
	 *                   file. If unknown, use {@code -1}
	 * @param col        the column where this statement happens in the source file.
	 *                   If unknown, use {@code -1}
	 * @param expression the expression to raise as error
	 */
	public Throw(CFG cfg, String sourceFile, int line, int col, Expression expression) {
		super(cfg, sourceFile, line, col);
		Objects.requireNonNull(expression, "The expression of a throw cannot be null");
		this.expression = expression;
	}

	/**
	 * Yields the expression that is being raised as error.
	 * 
	 * @return the expression being raised
	 */
	public final Expression getExpression() {
		return expression;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((expression == null) ? 0 : expression.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		Throw other = (Throw) obj;
		if (expression == null) {
			if (other.expression != null)
				return false;
		} else if (!expression.equals(other.expression))
			return false;
		return true;
	}

	@Override
	public final String toString() {
		return "throw " + expression;
	}
}