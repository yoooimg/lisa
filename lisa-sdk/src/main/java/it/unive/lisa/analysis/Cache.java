package it.unive.lisa.analysis;

import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import org.apache.commons.lang3.tuple.Pair;

public class Cache {
	static Map<Pair<Pair<ValueExpression, ValueExpression>,
			Pair<CodeLocation, BinaryOperator>>, InnerKey> keys = new LinkedHashMap<>();

	public static InnerKey createKey(BinaryExpression expression) {
		ValueExpression left = (ValueExpression) expression.getLeft();
		CodeLocation location = expression.getCodeLocation();
		ValueExpression right = (ValueExpression) expression.getRight();
		BinaryOperator operator = expression.getOperator();

		InnerKey key;
		if (keys.containsKey(Pair.of(Pair.of(left, right), Pair.of(location, operator)))) {
			key = keys.get(Pair.of(Pair.of(left, right), Pair.of(location, operator)));
		} else {
			key = new InnerKey(expression);
		}

		keys.put(Pair.of(Pair.of(key.left, key.right), Pair.of(key.location, key.operator)), key);
		return key;
	}

	public static <A extends AbstractState<A>> void putAnalysisStates(
			InnerKey key, AnalysisState<A> state,
			Pair<AnalysisState<A>, AnalysisState<A>> analysisStates) {
		key.putResult(state, analysisStates);
	}

	public static Pair<AnalysisState<?>, AnalysisState<?>> getAnalysisStates(InnerKey key, AnalysisState<?> state) {
		return key.getResult(state);
	}

	public static boolean containsKeyAndState(InnerKey key, AnalysisState<?> state) {
		return InnerKey.containsAll(key, state);
	}

	public static void clearCache() {
		for (InnerKey key : keys.values()) {
			key.clearAll();
		}
		keys.clear();
	}

	public static final class InnerKey {
		final ValueExpression left;
		final ValueExpression right;
		final CodeLocation location;
		final BinaryOperator operator;

		List<AnalysisState<?>> states = new LinkedList<>();
		Map<AnalysisState<?>, Pair<AnalysisState<?>, AnalysisState<?>>> analysisStates = new HashMap<>();

		InnerKey(BinaryExpression expression) {
			this.left = (ValueExpression) expression.getLeft();
			this.right = (ValueExpression) expression.getRight();
			this.location = expression.getCodeLocation();
			this.operator = expression.getOperator();
		}
		void addState(AnalysisState<?> state) {
			this.states.add(state);
		}

		static boolean containsKey(InnerKey key) {
			return keys.containsKey(Pair.of(Pair.of(key.left, key.right), Pair.of(key.location, key.operator)));
		}

		boolean containsState(AnalysisState<?> state) {
			return this.states.contains(state);
		}

		static boolean containsAll(InnerKey key, AnalysisState<?> state) {
			return containsKey(key) && key.containsState(state);
		}

		Pair<AnalysisState<?>, AnalysisState<?>> getResult(AnalysisState<?> state) {
            return this.analysisStates.get(state);
		}

		<A extends AbstractState<A>> void putResult(AnalysisState<A> state, Pair<AnalysisState<A>,
				AnalysisState<A>> analysisStates) {
			this.addState(state);
			this.analysisStates.put(state, Pair.of(analysisStates.getLeft(),  analysisStates.getRight()));
		}
		void clearStates() {
			this.states.clear();
		}
		void clearAnalysisStates() {
			this.analysisStates.clear();
		}
		void clearAll() {
			clearStates();
			clearAnalysisStates();
		}
	}
}
