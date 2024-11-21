package it.unive.lisa.program.cfg.statement;

import it.unive.lisa.analysis.AbstractState;
import it.unive.lisa.analysis.AnalysisState;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.StatementStore;
import it.unive.lisa.interprocedural.InterproceduralAnalysis;
import it.unive.lisa.program.cfg.CFG;
import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.program.cfg.statement.evaluation.EvaluationOrder;
import it.unive.lisa.program.cfg.statement.evaluation.RightToLeftEvaluation;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.type.Type;
import it.unive.lisa.type.Untyped;

/**
 * A statement assigning the result of an expression to an assignable
 * expression.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class Assignment extends BinaryExpression {

	/**
	 * Builds the assignment, assigning {@code expression} to {@code target},
	 * happening at the given location in the program. The static type of this
	 * expression is {@link Untyped}. The {@link EvaluationOrder} is
	 * {@link RightToLeftEvaluation}.
	 * 
	 * @param cfg        the cfg that this statement belongs to
	 * @param location   the location where this statement is defined within the
	 *                       program
	 * @param target     the target of the assignment
	 * @param expression the expression to assign to {@code target}
	 */
	public Assignment(
			CFG cfg,
			CodeLocation location,
			Expression target,
			Expression expression) {
		super(cfg, location, "=", RightToLeftEvaluation.INSTANCE, target, expression);
	}

	/**
	 * Builds the assignment, assigning {@code expression} to {@code target},
	 * happening at the given location in the program. The static type of this
	 * expression is {@link Untyped}.
	 * 
	 * @param cfg        the cfg that this statement belongs to
	 * @param location   the location where this statement is defined within the
	 *                       program
	 * @param order      the evaluation order of the sub-expressions
	 * @param target     the target of the assignment
	 * @param expression the expression to assign to {@code target}
	 */
	public Assignment(
			CFG cfg,
			CodeLocation location,
			EvaluationOrder order,
			Expression target,
			Expression expression) {
		super(cfg, location, "=", order, target, expression);
	}

	/**
	 * Builds the assignment, assigning {@code expression} to {@code target},
	 * happening at the given location in the program. The
	 * {@link EvaluationOrder} is {@link RightToLeftEvaluation}.
	 * 
	 * @param cfg        the cfg that this statement belongs to
	 * @param location   the location where this statement is defined within the
	 *                       program
	 * @param staticType the static type of this expression
	 * @param target     the target of the assignment
	 * @param expression the expression to assign to {@code target}
	 */
	public Assignment(
			CFG cfg,
			CodeLocation location,
			Type staticType,
			Expression target,
			Expression expression) {
		super(cfg, location, "=", RightToLeftEvaluation.INSTANCE, staticType, target, expression);
	}

	/**
	 * Builds the assignment, assigning {@code expression} to {@code target},
	 * happening at the given location in the program.
	 * 
	 * @param cfg        the cfg that this statement belongs to
	 * @param location   the location where this statement is defined within the
	 *                       program
	 * @param order      the evaluation order of the sub-expressions
	 * @param staticType the static type of this expression
	 * @param target     the target of the assignment
	 * @param expression the expression to assign to {@code target}
	 */
	public Assignment(
			CFG cfg,
			CodeLocation location,
			EvaluationOrder order,
			Type staticType,
			Expression target,
			Expression expression) {
		super(cfg, location, "=", order, staticType, target, expression);
	}

	@Override
	protected int compareSameClassAndParams(
			Statement o) {
		return 0; // no extra fields to compare
	}

	@Override
	public final String toString() {
		return getLeft() + " = " + getRight();
	}

	@Override
	public <A extends AbstractState<A>> AnalysisState<A> fwdBinarySemantics(
			InterproceduralAnalysis<A> interprocedural,
			AnalysisState<A> state,
			SymbolicExpression left,
			SymbolicExpression right,
			StatementStore<A> expressions)
			throws SemanticException {
		return state.assign(left, right, this);
	}
}
