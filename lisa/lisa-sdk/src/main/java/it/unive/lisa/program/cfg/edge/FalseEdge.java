package it.unive.lisa.program.cfg.edge;

import org.apache.commons.lang3.tuple.Pair;

import it.unive.lisa.analysis.AbstractState;
import it.unive.lisa.analysis.AnalysisState;
import it.unive.lisa.analysis.Cache;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.lattices.ExpressionSet;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;

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
		ExpressionSet exprs = state.getComputedExpressions();
		AnalysisState<A> result = state.bottom();
		for (SymbolicExpression expr : exprs) {
			
			if(expr instanceof BinaryExpression) {
				BinaryExpression binary = (BinaryExpression) expr;
				System.out.println("[AnalysisState]: the given expression is a binary expression");
				key = Cache.createKey(binary);

				if (Cache.containsKeyAndState(key, state)) {
					System.out.println("[Cache]: the given abstractState exist for the given key");
					return (AnalysisState<A>) Cache.getAnalysisStates(key, state).getRight();
				}

				System.out.println("[Cache]: doesn't contains splitted analysisStates for the given key and abstractState");
			}
			
			Pair<AnalysisState<A>, AnalysisState<A>> states = (Pair<AnalysisState<A>, AnalysisState<A>>) state.split(expr, getSource(), getDestination());
			
			System.out.println("[Split]: done!" );

			if (!(expr instanceof BinaryExpression)) {
				System.out.println("[AnalysisState]: the given expression is not a binary expression (Cache won't be touch)");
				System.out.println("[AnalysisState]: here the splitted analysisStates for the given not binary expression: " + states);
			}

			if(key != null)
				Cache.putAnalysisStates(key, state, states);

			
			AnalysisState<A> falseState = states.getRight();
			result = result.lub(falseState);
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
