package it.unive.lisa.program.cfg.edge;

import it.unive.lisa.analysis.AbstractState;
import it.unive.lisa.analysis.AnalysisState;
import it.unive.lisa.analysis.Cache;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.lattices.ExpressionSet;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.UnaryExpression;
import it.unive.lisa.symbolic.value.operator.unary.LogicalNegation;
import org.apache.commons.lang3.tuple.Pair;

/**
 * An edge connecting two statements, that is traversed when the condition
 * expressed in the source state does not hold. The abstract analysis state gets
 * modified by assuming that the statement where this edge originates does not
 * hold.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class FalseEdge extends Edge {

	/**
	 * Builds the edge.
	 * 
	 * @param source      the source statement
	 * @param destination the destination statement
	 */
	public FalseEdge(
			Statement source,
			Statement destination) {
		super(source, destination);
	}

	@Override
	public String toString() {
		return "[ " + getSource() + " ] -F-> [ " + getDestination() + " ]";
	}

	static Cache.InnerKey key;
	@SuppressWarnings("unchecked")
	@Override
	public <A extends AbstractState<A>> AnalysisState<A> traverseForward(
			AnalysisState<A> state)
			throws SemanticException {

		AnalysisState<?> falseState;
		Pair<AnalysisState<A>, AnalysisState<A>> splitResult;

		AnalysisState<A> result = state.bottom();
		ExpressionSet exprs = state.getComputedExpressions();

		for (SymbolicExpression expr : exprs) {
			if (expr instanceof BinaryExpression) {
				BinaryExpression binary = (BinaryExpression) expr;
				key = Cache.createKey(binary);

				if (Cache.containsKeyAndState(key, state)) {
					falseState = Cache.getAnalysisStates(key, state).getRight();
				} else {
					splitResult = state.split(binary, getSource(), getDestination());
					Cache.putAnalysisStates(key, state, splitResult);
					falseState = splitResult.getRight();
				}

			} else {
				UnaryExpression negExpr = new UnaryExpression(
						expr.getStaticType(),
						expr,
						LogicalNegation.INSTANCE,
						expr.getCodeLocation());
				falseState = state.assume(negExpr, getSource(), getDestination());
			}
			result = result.lub((AnalysisState<A>) falseState);
		}

		return result;
	}

	@Override
	public <A extends AbstractState<A>> AnalysisState<A> traverseBackwards(
			AnalysisState<A> state)
			throws SemanticException {
		return traverseForward(state);
	}

	@Override
	public boolean isUnconditional() {
		return false;
	}

	@Override
	public FalseEdge newInstance(
			Statement source,
			Statement destination) {
		return new FalseEdge(source, destination);
	}
}
