package it.unive.lisa.cfg.statement;

import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;

import it.unive.lisa.caches.Caches;
import it.unive.lisa.cfg.CFG;
import it.unive.lisa.cfg.type.Type;
import it.unive.lisa.cfg.type.Untyped;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.util.collections.ExternalSet;

/**
 * An expression that is part of a statement of the program.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public abstract class Expression extends Statement {

	/**
	 * The static type of this expression.
	 */
	private final Type staticType;

	private final ExternalSet<Type> runtimeTypes;

	/**
	 * The collection of meta variables that are generated by the evaluation of this
	 * expression. These should be removed as soon as the values computed by those
	 * gets out of scope (e.g., popped from the stack).
	 */
	private final Collection<Identifier> metaVariables;

	/**
	 * Builds an untyped expression happening at the given source location, that is
	 * its type is {@link Untyped#INSTANCE}.
	 * 
	 * @param cfg        the cfg that this expression belongs to
	 * @param sourceFile the source file where this expression happens. If
	 *                       unknown, use {@code null}
	 * @param line       the line number where this expression happens in the
	 *                       source file. If unknown, use {@code -1}
	 * @param col        the column where this expression happens in the source
	 *                       file. If unknown, use {@code -1}
	 */
	protected Expression(CFG cfg, String sourceFile, int line, int col) {
		this(cfg, sourceFile, line, col, Untyped.INSTANCE);
	}

	/**
	 * Builds a typed expression happening at the given source location.
	 * 
	 * @param cfg        the cfg that this expression belongs to
	 * @param sourceFile the source file where this expression happens. If
	 *                       unknown, use {@code null}
	 * @param line       the line number where this expression happens in the
	 *                       source file. If unknown, use {@code -1}
	 * @param col        the column where this expression happens in the source
	 *                       file. If unknown, use {@code -1}
	 * @param staticType the static type of this expression
	 */
	protected Expression(CFG cfg, String sourceFile, int line, int col, Type staticType) {
		super(cfg, sourceFile, line, col);
		Objects.requireNonNull(staticType, "The expression type of a CFG cannot be null");
		this.staticType = staticType;
		this.metaVariables = new HashSet<>();
		this.runtimeTypes = Caches.types().mkEmptySet();
	}

	/**
	 * Yields the static type of this expression.
	 * 
	 * @return the static type of this expression
	 */
	public final Type getStaticType() {
		return staticType;
	}
	
	protected final void setRuntimeTypes(ExternalSet<Type> runtimeTypes) {
		if (this.runtimeTypes == runtimeTypes || this.runtimeTypes.equals(runtimeTypes))
			return;
		
		this.runtimeTypes.clear();
		if (runtimeTypes != null && !runtimeTypes.isEmpty())
			this.runtimeTypes.addAll(runtimeTypes);
	}
	
	public final ExternalSet<Type> getRuntimeTypes() {
		if (runtimeTypes.isEmpty())
			return Caches.types().mkSingletonSet(staticType);
		return runtimeTypes;
	}
	
	public final Type getDynamicType() {
		ExternalSet<Type> runtimes = getRuntimeTypes();
		return runtimeTypes.reduce(runtimes.first(), (result, t) -> {
			if (result.canBeAssignedTo(t))
				return t;
			if (t.canBeAssignedTo(result))
				return result;
			return t.commonSupertype(result);
		});
	}

	/**
	 * Yields the meta variables that are generated by the evaluation of this
	 * expression. These should be removed as soon as the values computed by those
	 * gets out of scope (e.g., popped from the stack). The returned collection will
	 * be filled while evaluating this expression
	 * {@link #semantics(it.unive.lisa.analysis.AnalysisState, it.unive.lisa.analysis.callgraph.CallGraph, it.unive.lisa.cfg.CFG.ExpressionStates)},
	 * thus invoking this method before computing the semantics will yield an empty
	 * collection.
	 * 
	 * @return the meta variables
	 */
	public Collection<Identifier> getMetaVariables() {
		return metaVariables;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((staticType == null) ? 0 : staticType.hashCode());
		// we ignore the meta variables on purpose
		return result;
	}

	@Override
	public boolean isEqualTo(Statement st) {
		if (this == st)
			return true;
		if (!super.isEqualTo(st))
			return false;
		if (getClass() != st.getClass())
			return false;
		Expression other = (Expression) st;
		if (staticType == null) {
			if (other.staticType != null)
				return false;
		} else if (!staticType.equals(other.staticType))
			return false;
		// we ignore the meta variables on purpose
		return true;
	}
}
