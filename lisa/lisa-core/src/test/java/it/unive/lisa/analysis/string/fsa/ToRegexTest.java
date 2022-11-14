package it.unive.lisa.analysis.string.fsa;

import static org.junit.Assert.assertEquals;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import org.junit.Test;

public class ToRegexTest {

	@Test
	public void test01() {
		Set<State> states = new HashSet<>();
		State[] st = new State[1];
		st[0] = new State(true, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[0], "a"));

		Automaton a = new Automaton(states, delta);

		assertEquals("a*", a.toRegex());
	}

	@Test
	public void test02() {
		Set<State> states = new HashSet<>();
		State[] st = new State[2];
		st[0] = new State(true, false);
		st[1] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[0], "c"));
		delta.add(new Transition(st[0], st[1], "a"));
		delta.add(new Transition(st[1], st[0], "b"));
		delta.add(new Transition(st[1], st[1], "d"));

		Automaton a = new Automaton(states, delta);

		assertEquals(a.toRegex(), "(c*a)(d|bc*a)*");
	}

	@Test
	public void test03() {
		Set<State> states = new HashSet<>();
		State[] st = new State[3];

		st[0] = new State(true, false);
		st[1] = new State(false, true);
		st[2] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], "a"));
		delta.add(new Transition(st[0], st[2], "c"));

		// ab | cc
		Automaton a = new Automaton(states, delta);
		assertEquals(a.toRegex(), "(a|c)");
	}

	@Test
	public void test04() {
		Set<State> states = new HashSet<>();
		State[] st = new State[3];
		st[0] = new State(true, false);
		st[1] = new State(false, false);
		st[2] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], "a"));
		delta.add(new Transition(st[1], st[2], "b"));

		Automaton a = new Automaton(states, delta);
		assertEquals("ab", a.toRegex());
	}

	@Test
	public void test05() {
		Set<State> states = new HashSet<>();
		State[] st = new State[5];
		Set<Transition> delta = new HashSet<>();

		st[0] = new State(true, false);
		st[1] = new State(false, false);
		st[2] = new State(false, false);
		st[3] = new State(false, true);
		st[4] = new State(false, true);
		Collections.addAll(states, st);

		delta.add(new Transition(st[0], st[1], "a"));
		delta.add(new Transition(st[0], st[2], "c"));
		delta.add(new Transition(st[1], st[3], "b"));
		delta.add(new Transition(st[2], st[4], "c"));

		// ab | cc
		Automaton a = new Automaton(states, delta);

		assertEquals(a.toRegex(), "ab|cc");
	}

	@Test
	public void test06() {
		Set<State> states = new HashSet<>();
		State[] st = new State[4];
		st[0] = new State(true, false);
		st[1] = new State(false, false);
		st[2] = new State(false, true);
		st[3] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], ""));
		delta.add(new Transition(st[1], st[2], "a"));
		delta.add(new Transition(st[1], st[3], "b"));
		delta.add(new Transition(st[2], st[2], "c"));
		delta.add(new Transition(st[3], st[3], "c"));

		Automaton a = new Automaton(states, delta);

		assertEquals(a.toRegex(), "(a|b)c*");
	}

	@Test
	public void test07() {
		Set<State> states = new HashSet<>();
		State[] st = new State[4];
		st[0] = new State(true, false);
		st[1] = new State(false, false);
		st[2] = new State(false, false);
		st[3] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], "a"));
		delta.add(new Transition(st[0], st[2], "a"));
		delta.add(new Transition(st[1], st[3], "b"));
		delta.add(new Transition(st[2], st[3], "c"));

		Automaton a = new Automaton(states, delta);
		assertEquals(a.toRegex(), "a(b|c)");
	}

	@Test
	public void test08() {
		Set<State> states = new HashSet<>();
		State[] st = new State[2];
		st[0] = new State(true, false);
		st[1] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], "a"));

		Automaton a = new Automaton(states, delta);
		assertEquals(a.toRegex(), "a");
	}

	@Test
	public void test09() {
		Set<State> states = new HashSet<>();
		State[] st = new State[2];
		st[0] = new State(true, false);
		st[1] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], ""));

		Automaton a = new Automaton(states, delta);
		assertEquals(a.toRegex(), "");
	}

	@Test
	public void test10() {
		Set<State> states = new HashSet<>();
		State[] st = new State[2];
		st[0] = new State(true, false);
		st[1] = new State(false, true);
		Collections.addAll(states, st);

		Set<Transition> delta = new HashSet<>();
		delta.add(new Transition(st[0], st[1], "a"));
		delta.add(new Transition(st[1], st[1], "a"));
		delta.add(new Transition(st[1], st[1], "b"));

		Automaton a = new Automaton(states, delta);
		assertEquals(a.toRegex(), "a(a|b)*");
	}
}