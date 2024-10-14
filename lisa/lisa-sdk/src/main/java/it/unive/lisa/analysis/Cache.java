package it.unive.lisa.analysis;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.commons.lang3.tuple.Pair;

import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;

public class Cache {
    static Map<Pair<Pair<ValueExpression, ValueExpression>, Pair<CodeLocation, BinaryOperator>>,
            InnerKey> keys = new LinkedHashMap<>();

    public static InnerKey createKey(BinaryExpression expression) {
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

    public static  <A extends AbstractState<A>> void putAnalysisStates(InnerKey key, AnalysisState<A> state, Pair<AnalysisState<A>, AnalysisState<A>> analysisStates) {
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
        Map<AnalysisState<?>,
                Pair<AnalysisState<?>, AnalysisState<?>>> analysisStates = new HashMap<>();

       InnerKey(BinaryExpression expression) {
            this.left = (ValueExpression) expression.getLeft();
            this.right = (ValueExpression) expression.getRight();
            this.location = expression.getCodeLocation();
            this.operator = expression.getOperator();
        }

       void addState(AnalysisState<?> state) {
            this.states.add(state);
            System.out.println("[Cache]: put (into key) current state: " + state);
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
            Pair <AnalysisState<?>, AnalysisState<?>> results = this.analysisStates.get(state);
            AnalysisState<?> left = (AnalysisState<?>) results.getLeft();
            AnalysisState<?> right = (AnalysisState<?>) results.getRight();
            System.out.println("[Cache]: get pairOfAnalysisState for the given key and abstractState: " + Pair.of(left, right));
            return Pair.of(left, right);
        }

        <A extends AbstractState<A>> void putResult(AnalysisState<A> state, Pair<AnalysisState<A>, AnalysisState<A>> analysisStates) {
            this.addState(state);
            AnalysisState<?> left = analysisStates.getLeft();
            AnalysisState<?> right = analysisStates.getRight();
            this.analysisStates.put(state, Pair.of(left, right));
            System.out.println("[Cache]: add pairOfAnalysisState for the given key and abstractState: " + Pair.of(left, right));
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
