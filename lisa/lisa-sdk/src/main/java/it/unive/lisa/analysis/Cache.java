package it.unive.lisa.analysis;

import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import org.apache.commons.lang3.tuple.Pair;

import java.util.*;

public class Cache {
    static Map<Pair<Pair<ValueExpression, ValueExpression>, Pair<CodeLocation, BinaryOperator>>,
            InnerKey> keys = new LinkedHashMap<>();

    static InnerKey createKey(BinaryExpression expression) {
        ValueExpression left = (ValueExpression) expression.getLeft();
        CodeLocation location = expression.getCodeLocation();
        ValueExpression right = (ValueExpression) expression.getRight();
        BinaryOperator operator = expression.getOperator();

        InnerKey key;
        if(keys.containsKey(Pair.of(Pair.of(left, right), Pair.of(location, operator)))) {
           key = keys.get(Pair.of(Pair.of(left, right), Pair.of(location, operator)));
           System.out.println("[Cache]: get key for the given binary expression: " + expression);
        } else {
            key = new InnerKey(expression);
            System.out.println("[Cache]: create key for the given binary expression: " + expression);
        }
        keys.put(Pair.of(Pair.of(key.left, key.right), Pair.of(key.location, key.operator)), key);
        return key;
    }

    static <A extends AbstractState<A>> void putAnalysisStates(InnerKey key, A state, Pair<AnalysisState<A>, AnalysisState<A>> analysisStates) {
        key.putResult(state, analysisStates);
    }

    static <A extends AbstractState<A>> Pair<AnalysisState<A>, AnalysisState<A>> getAnalysisStates(InnerKey key, A state) {
        return key.getResult(state);
    }

    static <A extends AbstractState<A>> boolean containsKeyAndState(InnerKey key, A state) {
        return InnerKey.containsAll(key, state);
    }

    static final class InnerKey {
        final ValueExpression left;
        final ValueExpression right;
        final CodeLocation location;
        final BinaryOperator operator;

        List<AbstractState<?>> states = new LinkedList<>();
        Map<AbstractState<?>,
                Pair<AnalysisState<?>, AnalysisState<?>>> analysisStates = new HashMap<>();

       InnerKey(BinaryExpression expression) {
            this.left = (ValueExpression) expression.getLeft();
            this.right = (ValueExpression) expression.getRight();
            this.location = expression.getCodeLocation();
            this.operator = expression.getOperator();
        }

        <A extends AbstractState<A>> void addState(A state) {
            this.states.add(state);
            System.out.println("[Cache]: put (into key) current state: " + state);
        }

        static boolean containsKey(InnerKey key) {
            return keys.containsKey(Pair.of(Pair.of(key.left, key.right), Pair.of(key.location, key.operator)));
        }

        <A extends AbstractState<A>> boolean containsState(A state) {
            return this.states.contains(state);
        }

        static <A extends AbstractState<A>> boolean containsAll(InnerKey key, A state) {
            return containsKey(key) && key.containsState(state);
        }

        @SuppressWarnings("unchecked")
        <A extends AbstractState<A>> Pair<AnalysisState<A>, AnalysisState<A>> getResult(A state) {
            Pair <AnalysisState<?>, AnalysisState<?>> results = this.analysisStates.get(state);
            AnalysisState<A> left = (AnalysisState<A>) results.getLeft();
            AnalysisState<A> right = (AnalysisState<A>) results.getRight();
            System.out.println("[Cache]: get pairOfAnalysisState for the given key and abstractState: " + Pair.of(left, right));
            return Pair.of(left, right);
        }

        <A extends AbstractState<A>> void putResult(A state, Pair<AnalysisState<A>, AnalysisState<A>> analysisStates) {
            this.addState(state);
            AnalysisState<?> left = analysisStates.getLeft();
            AnalysisState<?> right = analysisStates.getRight();
            this.analysisStates.put(state, Pair.of(left, right));
            System.out.println("[Cache]: add pairOfAnalysisState for the given key and abstractState: " + Pair.of(left, right));
        }
    }
}
