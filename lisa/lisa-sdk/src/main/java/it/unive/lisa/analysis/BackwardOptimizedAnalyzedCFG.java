package it.unive.lisa.analysis;

import it.unive.lisa.analysis.lattices.ExpressionSet;
import it.unive.lisa.analysis.symbols.SymbolAliasing;
import it.unive.lisa.conf.FixpointConfiguration;
import it.unive.lisa.conf.LiSAConfiguration;
import it.unive.lisa.interprocedural.FixpointResults;
import it.unive.lisa.interprocedural.InterproceduralAnalysis;
import it.unive.lisa.interprocedural.InterproceduralAnalysisException;
import it.unive.lisa.interprocedural.OpenCallPolicy;
import it.unive.lisa.interprocedural.ScopeId;
import it.unive.lisa.interprocedural.callgraph.CallGraph;
import it.unive.lisa.interprocedural.callgraph.CallResolutionException;
import it.unive.lisa.logging.TimerLogger;
import it.unive.lisa.program.Application;
import it.unive.lisa.program.cfg.CFG;
import it.unive.lisa.program.cfg.edge.Edge;
import it.unive.lisa.program.cfg.fixpoints.BackwardAscendingFixpoint;
import it.unive.lisa.program.cfg.fixpoints.CFGFixpoint.CompoundState;
import it.unive.lisa.program.cfg.fixpoints.OptimizedBackwardFixpoint;
import it.unive.lisa.program.cfg.statement.Expression;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.program.cfg.statement.call.CFGCall;
import it.unive.lisa.program.cfg.statement.call.Call;
import it.unive.lisa.program.cfg.statement.call.OpenCall;
import it.unive.lisa.program.cfg.statement.call.UnresolvedCall;
import it.unive.lisa.type.Type;
import it.unive.lisa.util.collections.workset.FIFOWorkingSet;
import it.unive.lisa.util.collections.workset.WorkingSet;
import it.unive.lisa.util.datastructures.graph.algorithms.BackwardFixpoint;
import it.unive.lisa.util.datastructures.graph.algorithms.FixpointException;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A {@link BackwardAnalyzedCFG} that has been built using an
 * {@link OptimizedBackwardFixpoint}. This means that this graph will only
 * contain results for widening points (that is, {@link Statement}s that part of
 * {@link #getCycleEntries()}), exit statements (that is, {@link Statement}s
 * such that {@link Statement#stopsExecution()} holds), and hotspots (that is,
 * {@link Statement}s such that {@link LiSAConfiguration#hotspots} holds).
 * Approximations for other statements can be retrieved through
 * {@link #getUnwindedAnalysisStateBefore(Statement, FixpointConfiguration)},
 * that will first expand the results using
 * {@link #unwind(FixpointConfiguration)}.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 * 
 * @param <A> the type of {@link AbstractState} contained into the analysis
 *                state
 */
public class BackwardOptimizedAnalyzedCFG<A extends AbstractState<A>> extends BackwardAnalyzedCFG<A> {

	private static final Logger LOG = LogManager.getLogger(BackwardOptimizedAnalyzedCFG.class);

	private final InterproceduralAnalysis<A> interprocedural;

	private StatementStore<A> expanded;

	/**
	 * Builds the control flow graph, storing the given mapping between nodes
	 * and fixpoint computation results.
	 * 
	 * @param cfg             the original control flow graph
	 * @param id              a {@link ScopeId} meant to identify this specific
	 *                            result based on how it has been produced
	 * @param singleton       an instance of the {@link AnalysisState}
	 *                            containing the abstract state of the analysis
	 *                            that was executed, used to retrieve top and
	 *                            bottom values
	 * @param interprocedural the analysis that have been used to produce this
	 *                            result, and that can be used to unwind the
	 *                            results
	 */
	public BackwardOptimizedAnalyzedCFG(
			CFG cfg,
			ScopeId id,
			AnalysisState<A> singleton,
			InterproceduralAnalysis<A> interprocedural) {
		super(cfg, id, singleton);
		this.interprocedural = interprocedural;
	}

	/**
	 * Builds the control flow graph, storing the given mapping between nodes
	 * and fixpoint computation results.
	 * 
	 * @param cfg             the original control flow graph
	 * @param id              a {@link ScopeId} meant to identify this specific
	 *                            result based on how it has been produced
	 * @param singleton       an instance of the {@link AnalysisState}
	 *                            containing the abstract state of the analysis
	 *                            that was executed, used to retrieve top and
	 *                            bottom values
	 * @param entryStates     the entry state for each entry point of the cfg
	 * @param results         the results of the fixpoint computation
	 * @param interprocedural the analysis that have been used to produce this
	 *                            result, and that can be used to unwind the
	 *                            results
	 */
	public BackwardOptimizedAnalyzedCFG(
			CFG cfg,
			ScopeId id,
			AnalysisState<A> singleton,
			Map<Statement, AnalysisState<A>> entryStates,
			Map<Statement, AnalysisState<A>> results,
			InterproceduralAnalysis<A> interprocedural) {
		super(cfg, id, singleton, entryStates, results);
		this.interprocedural = interprocedural;
	}

	/**
	 * Builds the control flow graph, storing the given mapping between nodes
	 * and fixpoint computation results.
	 * 
	 * @param cfg             the original control flow graph
	 * @param id              a {@link ScopeId} meant to identify this specific
	 *                            result based on how it has been produced
	 * @param entryStates     the entry state for each entry point of the cfg
	 * @param results         the results of the fixpoint computation
	 * @param interprocedural the analysis that have been used to produce this
	 *                            result, and that can be used to unwind the
	 *                            results
	 */
	public BackwardOptimizedAnalyzedCFG(
			CFG cfg,
			ScopeId id,
			StatementStore<A> entryStates,
			StatementStore<A> results,
			InterproceduralAnalysis<A> interprocedural) {
		super(cfg, id, entryStates, results);
		this.interprocedural = interprocedural;
	}

	private BackwardOptimizedAnalyzedCFG(
			CFG cfg,
			ScopeId id,
			StatementStore<A> entryStates,
			StatementStore<A> results,
			StatementStore<A> expanded,
			InterproceduralAnalysis<A> interprocedural) {
		super(cfg, id, entryStates, results);
		this.interprocedural = interprocedural;
		this.expanded = expanded;
	}

	/**
	 * Yields the computed result at a given statement (exit state). If such a
	 * state is not available as it was discarded due to optimization, and
	 * fixpoint's results have not been unwinded yet, a fixpoint iteration is
	 * executed in-place through {@link #unwind(FixpointConfiguration)}.
	 *
	 * @param st   the statement
	 * @param conf the {@link FixpointConfiguration} to use for running the fast
	 *                 fixpoint computation
	 *
	 * @return the result computed at the given statement
	 */
	public AnalysisState<A> getUnwindedAnalysisStateBefore(
			Statement st,
			FixpointConfiguration conf) {
		if (results.getKeys().contains(st))
			return results.getState(st);

		if (expanded != null)
			return expanded.getState(st);

		unwind(conf);

		return expanded.getState(st);
	}

	/**
	 * Runs an ascending fixpoint computation starting with the results
	 * available in this graph, with the purpose of propagating the
	 * approximations held in this result to all the missing nodes.
	 * 
	 * @param conf the {@link FixpointConfiguration} to use for running the fast
	 *                 fixpoint computation
	 */
	public void unwind(
			FixpointConfiguration conf) {
		AnalysisState<A> bottom = results.lattice.bottom();
		StatementStore<A> bot = new StatementStore<>(bottom);
		Map<Statement, CompoundState<A>> starting = new HashMap<>();
		for (Entry<Statement, AnalysisState<A>> entry : exitStates)
			starting.put(entry.getKey(), CompoundState.of(entry.getValue(), bot));

		Map<Statement, CompoundState<A>> existing = new HashMap<>();
		CompoundState<A> fallback = CompoundState.of(bottom, bot);
		for (Entry<Statement, AnalysisState<A>> entry : results) {
			Statement stmt = entry.getKey();
			AnalysisState<A> approx = entry.getValue();
			CompoundState<A> def = existing.getOrDefault(stmt, fallback);

			if (!(stmt instanceof Expression) || ((Expression) stmt).getRootStatement() == stmt)
				existing.put(stmt, CompoundState.of(approx, def.intermediateStates));
			else {
				Expression e = (Expression) stmt;
				CompoundState<A> val = existing.computeIfAbsent(e.getRootStatement(),
						ex -> CompoundState.of(bottom, bot.bottom()));
				val.intermediateStates.put(e, approx);
			}
		}

		BackwardAscendingFixpoint<A> asc = new BackwardAscendingFixpoint<>(this, new PrecomputedAnalysis(), conf);
		BackwardFixpoint<CFG, Statement, Edge, CompoundState<A>> fix = new BackwardFixpoint<>(this, true);
		TimerLogger.execAction(LOG, "Unwinding optimizied results of " + this, () -> {
			try {
				Map<Statement, CompoundState<A>> res = fix.fixpoint(
						starting,
						FIFOWorkingSet.mk(),
						asc,
						existing);
				expanded = new StatementStore<>(bottom);
				for (Entry<Statement, CompoundState<A>> e : res.entrySet()) {
					expanded.put(e.getKey(), e.getValue().postState);
					for (Entry<Statement, AnalysisState<A>> ee : e.getValue().intermediateStates)
						expanded.put(ee.getKey(), ee.getValue());
				}
			} catch (FixpointException e) {
				LOG.error("Unable to unwind optimized results of " + this, e);
			}
		});
	}

	/**
	 * Yields whether or not the non-unwinded results of this cfg contain the
	 * prestate of the given statement.
	 * 
	 * @param st the statement
	 * 
	 * @return whether or not a prestate for {@code st} exists
	 */
	public boolean hasPreStateOf(
			Statement st) {
		return results.getKeys().contains(st);
	}

	/**
	 * Stores the given prestate for the statement in the non-unwinded results
	 * of this cfg, overwriting any existing value.
	 * 
	 * @param st       the statement
	 * @param prestate the prestate
	 */
	public void storePreStateOf(
			Statement st,
			AnalysisState<A> prestate) {
		results.put(st, prestate);
	}

	private class PrecomputedAnalysis implements InterproceduralAnalysis<A> {

		@Override
		public void init(
				Application app,
				CallGraph callgraph,
				OpenCallPolicy policy)
				throws InterproceduralAnalysisException {
			throw new UnsupportedOperationException();
		}

		@Override
		public void fixpoint(
				AnalysisState<A> entryState,
				Class<? extends WorkingSet<Statement>> fixpointWorkingSet,
				FixpointConfiguration conf)
				throws FixpointException {
			throw new UnsupportedOperationException();
		}

		@Override
		public Collection<AnalyzedCFG<A>> getAnalysisResultsOf(
				CFG cfg) {
			throw new UnsupportedOperationException();
		}

		@Override
		public AnalysisState<A> getAbstractResultOf(
				CFGCall call,
				AnalysisState<A> entryState,
				ExpressionSet[] parameters,
				StatementStore<A> expressions)
				throws SemanticException {
			Call source = call.getSource() == null ? call : call.getSource();
			if (results.getKeys().contains(source))
				return results.getState(source);

			FixpointResults<A> precomputed = interprocedural.getFixpointResults();
			ScopeToken scope = new ScopeToken(call);
			ScopeId id = getId().push(call);
			AnalysisState<A> state = entryState.bottom();
			for (CFG target : call.getTargetedCFGs()) {
				AnalysisState<A> res = precomputed.getState(target).getState(id).getExitState();
				state = state.lub(unscope(call, scope, res));
			}
			return state;
		}

		@Override
		public AnalysisState<A> getAbstractResultOf(
				OpenCall call,
				AnalysisState<A> entryState,
				ExpressionSet[] parameters,
				StatementStore<A> expressions)
				throws SemanticException {
			return interprocedural.getAbstractResultOf(call, entryState, parameters, expressions);
		}

		@Override
		public Call resolve(
				UnresolvedCall call,
				Set<Type>[] types,
				SymbolAliasing aliasing)
				throws CallResolutionException {
			return interprocedural.resolve(call, types, aliasing);
		}

		@Override
		public FixpointResults<A> getFixpointResults() {
			return interprocedural.getFixpointResults();
		}

		@Override
		public boolean needsCallGraph() {
			// not really needed
			return false;
		}
	}

	@Override
	public BackwardOptimizedAnalyzedCFG<A> lubAux(
			BackwardAnalyzedCFG<A> other)
			throws SemanticException {
		if (!getDescriptor().equals(other.getDescriptor()) || !sameIDs(other)
				|| !(other instanceof BackwardOptimizedAnalyzedCFG<?>))
			throw new SemanticException(CANNOT_LUB_ERROR);

		BackwardOptimizedAnalyzedCFG<A> o = (BackwardOptimizedAnalyzedCFG<A>) other;
		return new BackwardOptimizedAnalyzedCFG<A>(
				this,
				id,
				exitStates.lub(other.exitStates),
				results.lub(other.results),
				expanded == null ? o.expanded : expanded.lub(o.expanded),
				interprocedural);
	}

	@Override
	public BackwardOptimizedAnalyzedCFG<A> glbAux(
			BackwardAnalyzedCFG<A> other)
			throws SemanticException {
		if (!getDescriptor().equals(other.getDescriptor()) || !sameIDs(other)
				|| !(other instanceof BackwardOptimizedAnalyzedCFG<?>))
			throw new SemanticException(CANNOT_GLB_ERROR);

		BackwardOptimizedAnalyzedCFG<A> o = (BackwardOptimizedAnalyzedCFG<A>) other;
		return new BackwardOptimizedAnalyzedCFG<A>(
				this,
				id,
				exitStates.glb(other.exitStates),
				results.glb(other.results),
				expanded == null ? o.expanded : expanded.glb(o.expanded),
				interprocedural);
	}

	@Override
	public BackwardOptimizedAnalyzedCFG<A> wideningAux(
			BackwardAnalyzedCFG<A> other)
			throws SemanticException {
		if (!getDescriptor().equals(other.getDescriptor()) || !sameIDs(other)
				|| !(other instanceof BackwardOptimizedAnalyzedCFG<?>))
			throw new SemanticException(CANNOT_WIDEN_ERROR);

		BackwardOptimizedAnalyzedCFG<A> o = (BackwardOptimizedAnalyzedCFG<A>) other;
		return new BackwardOptimizedAnalyzedCFG<A>(
				this,
				id,
				exitStates.widening(other.exitStates),
				results.widening(other.results),
				expanded == null ? o.expanded : expanded.widening(o.expanded),
				interprocedural);
	}

	@Override
	public BackwardOptimizedAnalyzedCFG<A> narrowingAux(
			BackwardAnalyzedCFG<A> other)
			throws SemanticException {
		if (!getDescriptor().equals(other.getDescriptor()) || !sameIDs(other)
				|| !(other instanceof BackwardOptimizedAnalyzedCFG<?>))
			throw new SemanticException(CANNOT_NARROW_ERROR);

		BackwardOptimizedAnalyzedCFG<A> o = (BackwardOptimizedAnalyzedCFG<A>) other;
		return new BackwardOptimizedAnalyzedCFG<A>(
				this,
				id,
				exitStates.narrowing(other.exitStates),
				results.narrowing(other.results),
				expanded == null ? o.expanded : expanded.narrowing(o.expanded),
				interprocedural);
	}

	@Override
	public BackwardOptimizedAnalyzedCFG<A> top() {
		return new BackwardOptimizedAnalyzedCFG<>(this, id.startingId(), exitStates.top(), results.top(), null, null);
	}

	@Override
	public BackwardOptimizedAnalyzedCFG<A> bottom() {
		return new BackwardOptimizedAnalyzedCFG<>(this, id.startingId(), exitStates.bottom(), results.bottom(), null,
				null);
	}
}
