package it.unive.lisa.outputs;

import static org.junit.Assert.assertEquals;

import it.unive.lisa.TestLanguageFeatures;
import it.unive.lisa.TestTypeSystem;
import it.unive.lisa.outputs.serializableGraph.SerializableCFG;
import it.unive.lisa.outputs.serializableGraph.SerializableEdge;
import it.unive.lisa.outputs.serializableGraph.SerializableGraph;
import it.unive.lisa.outputs.serializableGraph.SerializableNode;
import it.unive.lisa.program.ClassUnit;
import it.unive.lisa.program.Program;
import it.unive.lisa.program.SyntheticLocation;
import it.unive.lisa.program.cfg.CFG;
import it.unive.lisa.program.cfg.CodeMemberDescriptor;
import it.unive.lisa.program.cfg.edge.Edge;
import it.unive.lisa.program.cfg.edge.FalseEdge;
import it.unive.lisa.program.cfg.edge.SequentialEdge;
import it.unive.lisa.program.cfg.edge.TrueEdge;
import it.unive.lisa.program.cfg.statement.Assignment;
import it.unive.lisa.program.cfg.statement.Return;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.program.cfg.statement.VariableRef;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import org.junit.Test;

public class SerializableGraphTest {

	private static final ClassUnit unit = new ClassUnit(SyntheticLocation.INSTANCE,
			new Program(new TestLanguageFeatures(), new TestTypeSystem()), "Testing", false);

	private static void addNode(
			SortedSet<SerializableNode> nodes,
			Statement st,
			int offset,
			int... inner) {
		List<Integer> list = new ArrayList<>(inner.length);
		for (int i = 0; i < inner.length; i++)
			list.add(inner[i]);
		nodes.add(new SerializableNode(offset, list, st.toString()));
	}

	private static void addEdge(
			SortedSet<SerializableEdge> edges,
			Edge e,
			int src,
			int dest) {
		edges.add(new SerializableEdge(src, dest, e.getClass().getSimpleName()));
	}

	@Test
	public void testSimpleIf() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "simpleIf"));

		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef c3 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "3");
		VariableRef c4 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "4");
		VariableRef lvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "l");
		VariableRef rvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "r");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		Assignment condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Assignment a1 = new Assignment(cfg, SyntheticLocation.INSTANCE, lvar, c3);
		Assignment a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, rvar, c4);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, xvar);

		cfg.addNode(condition, true);
		cfg.addNode(a1);
		cfg.addNode(a2);
		cfg.addNode(ret);

		Edge e1 = new TrueEdge(condition, a1);
		Edge e2 = new FalseEdge(condition, a2);
		Edge e3 = new SequentialEdge(a1, ret);
		Edge e4 = new SequentialEdge(a2, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		cfg.addEdge(e3);
		cfg.addEdge(e4);

		SerializableGraph graph = SerializableCFG.fromCFG(cfg);

		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();

		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, condition, 0, 1, 2);
		addNode(nodes, lvar, 4);
		addNode(nodes, c3, 5);
		addNode(nodes, a1, 3, 4, 5);
		addNode(nodes, rvar, 7);
		addNode(nodes, c4, 8);
		addNode(nodes, a2, 6, 7, 8);
		addNode(nodes, xvar, 10);
		addNode(nodes, ret, 9, 10);

		addEdge(edges, e1, 0, 3);
		addEdge(edges, e2, 0, 6);
		addEdge(edges, e3, 3, 9);
		addEdge(edges, e4, 6, 9);

		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

	@Test
	public void testEmptyIf() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "emptyIf"));
		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		Assignment condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, xvar);
		cfg.addNode(condition, true);
		cfg.addNode(ret);
		Edge e1 = new TrueEdge(condition, ret);
		Edge e2 = new FalseEdge(condition, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		SerializableGraph graph = SerializableCFG.fromCFG(cfg);
		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();
		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, condition, 0, 1, 2);
		addNode(nodes, xvar, 4);
		addNode(nodes, ret, 3, 4);
		addEdge(edges, e1, 0, 3);
		addEdge(edges, e2, 0, 3);
		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

	@Test
	public void testIfWithEmptyBranch() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "emptyBranch"));
		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef c3 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "3");
		VariableRef c4 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "4");
		VariableRef lvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "l");
		VariableRef rvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "r");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		Assignment condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Assignment a1 = new Assignment(cfg, SyntheticLocation.INSTANCE, lvar, c3);
		Assignment a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, rvar, c4);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, xvar);
		cfg.addNode(condition, true);
		cfg.addNode(a1);
		cfg.addNode(a2);
		cfg.addNode(ret);
		Edge e1 = new TrueEdge(condition, a1);
		Edge e2 = new FalseEdge(condition, ret);
		Edge e3 = new SequentialEdge(a1, a2);
		Edge e4 = new SequentialEdge(a2, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		cfg.addEdge(e3);
		cfg.addEdge(e4);
		SerializableGraph graph = SerializableCFG.fromCFG(cfg);
		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();
		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, condition, 0, 1, 2);
		addNode(nodes, lvar, 4);
		addNode(nodes, c3, 5);
		addNode(nodes, a1, 3, 4, 5);
		addNode(nodes, rvar, 7);
		addNode(nodes, c4, 8);
		addNode(nodes, a2, 6, 7, 8);
		addNode(nodes, xvar, 10);
		addNode(nodes, ret, 9, 10);
		addEdge(edges, e1, 0, 3);
		addEdge(edges, e2, 0, 9);
		addEdge(edges, e3, 3, 6);
		addEdge(edges, e4, 6, 9);
		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

	@Test
	public void testAsymmetricIf() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "asymmetricIf"));
		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef c3 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "3");
		VariableRef c4 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "4");
		VariableRef c5 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "5");
		VariableRef lvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "l");
		VariableRef rvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "r");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		VariableRef yvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "y");
		Assignment condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Assignment a1 = new Assignment(cfg, SyntheticLocation.INSTANCE, lvar, c3);
		Assignment a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, rvar, c4);
		Assignment a3 = new Assignment(cfg, SyntheticLocation.INSTANCE, xvar, c5);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, yvar);
		cfg.addNode(condition, true);
		cfg.addNode(a1);
		cfg.addNode(a2);
		cfg.addNode(a3);
		cfg.addNode(ret);
		Edge e1 = new TrueEdge(condition, a1);
		Edge e2 = new FalseEdge(condition, a2);
		Edge e3 = new SequentialEdge(a1, a3);
		Edge e4 = new SequentialEdge(a2, ret);
		Edge e5 = new SequentialEdge(a3, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		cfg.addEdge(e3);
		cfg.addEdge(e4);
		cfg.addEdge(e5);
		SerializableGraph graph = SerializableCFG.fromCFG(cfg);
		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();
		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, condition, 0, 1, 2);
		addNode(nodes, lvar, 4);
		addNode(nodes, c3, 5);
		addNode(nodes, a1, 3, 4, 5);
		addNode(nodes, rvar, 7);
		addNode(nodes, c4, 8);
		addNode(nodes, a2, 6, 7, 8);
		addNode(nodes, xvar, 10);
		addNode(nodes, c5, 11);
		addNode(nodes, a3, 9, 10, 11);
		addNode(nodes, yvar, 13);
		addNode(nodes, ret, 12, 13);
		addEdge(edges, e1, 0, 3);
		addEdge(edges, e2, 0, 6);
		addEdge(edges, e3, 3, 9);
		addEdge(edges, e4, 6, 12);
		addEdge(edges, e5, 9, 12);
		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

	@Test
	public void testSimpleLoop() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "simpleLoop"));
		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef c3 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "3");
		VariableRef c4 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "4");
		VariableRef lvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "l");
		VariableRef rvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "r");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		Assignment condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Assignment a1 = new Assignment(cfg, SyntheticLocation.INSTANCE, lvar, c3);
		Assignment a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, rvar, c4);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, xvar);
		cfg.addNode(condition, true);
		cfg.addNode(a1);
		cfg.addNode(a2);
		cfg.addNode(ret);
		Edge e1 = new TrueEdge(condition, a1);
		Edge e2 = new FalseEdge(condition, a2);
		Edge e3 = new SequentialEdge(a1, condition);
		Edge e4 = new SequentialEdge(a2, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		cfg.addEdge(e3);
		cfg.addEdge(e4);
		SerializableGraph graph = SerializableCFG.fromCFG(cfg);
		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();
		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, condition, 0, 1, 2);
		addNode(nodes, lvar, 4);
		addNode(nodes, c3, 5);
		addNode(nodes, a1, 3, 4, 5);
		addNode(nodes, rvar, 7);
		addNode(nodes, c4, 8);
		addNode(nodes, a2, 6, 7, 8);
		addNode(nodes, xvar, 10);
		addNode(nodes, ret, 9, 10);
		addEdge(edges, e1, 0, 3);
		addEdge(edges, e2, 0, 6);
		addEdge(edges, e3, 3, 0);
		addEdge(edges, e4, 6, 9);
		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

	@Test
	public void testEmptyLoop() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "emptyLoop"));
		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef c4 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "4");
		VariableRef rvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "r");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		Assignment condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Assignment a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, rvar, c4);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, xvar);
		cfg.addNode(condition, true);
		cfg.addNode(a2);
		cfg.addNode(ret);
		Edge e1 = new TrueEdge(condition, condition);
		Edge e2 = new FalseEdge(condition, a2);
		Edge e4 = new SequentialEdge(a2, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		cfg.addEdge(e4);
		SerializableGraph graph = SerializableCFG.fromCFG(cfg);
		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();
		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, condition, 0, 1, 2);
		addNode(nodes, rvar, 4);
		addNode(nodes, c4, 5);
		addNode(nodes, a2, 3, 4, 5);
		addNode(nodes, xvar, 7);
		addNode(nodes, ret, 6, 7);
		addEdge(edges, e1, 0, 0);
		addEdge(edges, e2, 0, 3);
		addEdge(edges, e4, 3, 6);
		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

	@Test
	public void testNestedConditionals() {
		CFG cfg = new CFG(new CodeMemberDescriptor(SyntheticLocation.INSTANCE, unit, false, "nested"));
		VariableRef c1 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "1");
		VariableRef c2 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "2");
		VariableRef c3 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "3");
		VariableRef c4 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "4");
		VariableRef c5 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "5");
		VariableRef c6 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "6");
		VariableRef c7 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "7");
		VariableRef c8 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "8");
		VariableRef c9 = new VariableRef(cfg, SyntheticLocation.INSTANCE, "9");
		VariableRef loop_a1var = new VariableRef(cfg, SyntheticLocation.INSTANCE, "loop_a1");
		VariableRef loop_a2var = new VariableRef(cfg, SyntheticLocation.INSTANCE, "loop_a2");
		VariableRef if_a1var = new VariableRef(cfg, SyntheticLocation.INSTANCE, "if_a1");
		VariableRef if_a2var = new VariableRef(cfg, SyntheticLocation.INSTANCE, "if_a2");
		VariableRef if_a3var = new VariableRef(cfg, SyntheticLocation.INSTANCE, "if_a3");
		VariableRef xvar = new VariableRef(cfg, SyntheticLocation.INSTANCE, "x");
		Assignment loop_condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c1, c2);
		Assignment loop_a1 = new Assignment(cfg, SyntheticLocation.INSTANCE, loop_a1var, c3);
		Assignment loop_a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, loop_a2var, c4);
		Assignment if_condition = new Assignment(cfg, SyntheticLocation.INSTANCE, c5, c6);
		Assignment if_a1 = new Assignment(cfg, SyntheticLocation.INSTANCE, if_a1var, c7);
		Assignment if_a2 = new Assignment(cfg, SyntheticLocation.INSTANCE, if_a2var, c8);
		Assignment if_a3 = new Assignment(cfg, SyntheticLocation.INSTANCE, if_a3var, c9);
		Return ret = new Return(cfg, SyntheticLocation.INSTANCE, xvar);
		cfg.addNode(loop_condition, true);
		cfg.addNode(loop_a1);
		cfg.addNode(loop_a2);
		cfg.addNode(if_condition);
		cfg.addNode(if_a1);
		cfg.addNode(if_a2);
		cfg.addNode(if_a3);
		cfg.addNode(ret);
		Edge e1 = new TrueEdge(loop_condition, loop_a1);
		Edge e2 = new SequentialEdge(loop_a1, if_condition);
		Edge e3 = new TrueEdge(if_condition, if_a1);
		Edge e4 = new SequentialEdge(if_a1, if_a3);
		Edge e5 = new SequentialEdge(if_a3, loop_a2);
		Edge e6 = new FalseEdge(if_condition, if_a2);
		Edge e7 = new SequentialEdge(if_a2, loop_a2);
		Edge e8 = new SequentialEdge(loop_a2, loop_condition);
		Edge e9 = new FalseEdge(loop_condition, ret);
		cfg.addEdge(e1);
		cfg.addEdge(e2);
		cfg.addEdge(e3);
		cfg.addEdge(e4);
		cfg.addEdge(e5);
		cfg.addEdge(e6);
		cfg.addEdge(e7);
		cfg.addEdge(e8);
		cfg.addEdge(e9);
		SerializableGraph graph = SerializableCFG.fromCFG(cfg);
		SortedSet<SerializableNode> nodes = new TreeSet<>();
		SortedSet<SerializableEdge> edges = new TreeSet<>();
		addNode(nodes, c1, 1);
		addNode(nodes, c2, 2);
		addNode(nodes, loop_condition, 0, 1, 2);
		addNode(nodes, loop_a1var, 4);
		addNode(nodes, c3, 5);
		addNode(nodes, loop_a1, 3, 4, 5);
		addNode(nodes, loop_a2var, 7);
		addNode(nodes, c4, 8);
		addNode(nodes, loop_a2, 6, 7, 8);
		addNode(nodes, c5, 10);
		addNode(nodes, c6, 11);
		addNode(nodes, if_condition, 9, 10, 11);
		addNode(nodes, if_a1var, 13);
		addNode(nodes, c7, 14);
		addNode(nodes, if_a1, 12, 13, 14);
		addNode(nodes, if_a2var, 16);
		addNode(nodes, c8, 17);
		addNode(nodes, if_a2, 15, 16, 17);
		addNode(nodes, if_a3var, 19);
		addNode(nodes, c9, 20);
		addNode(nodes, if_a3, 18, 19, 20);
		addNode(nodes, xvar, 22);
		addNode(nodes, ret, 21, 22);
		addEdge(edges, e1, 0, 3);
		addEdge(edges, e2, 3, 9);
		addEdge(edges, e3, 9, 12);
		addEdge(edges, e4, 12, 18);
		addEdge(edges, e5, 18, 6);
		addEdge(edges, e6, 9, 15);
		addEdge(edges, e7, 15, 6);
		addEdge(edges, e8, 6, 0);
		addEdge(edges, e9, 0, 21);
		SerializableGraph expected = new SerializableGraph(
				cfg.getDescriptor().getFullSignatureWithParNames(),
				null,
				nodes,
				edges,
				Collections.emptySortedSet());
		assertEquals(expected, graph);
	}

}
