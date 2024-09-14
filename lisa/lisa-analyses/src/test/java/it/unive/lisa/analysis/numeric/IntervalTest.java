package it.unive.lisa.analysis.numeric;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import it.unive.lisa.TestParameterProvider;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.program.type.Int32Type;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.util.numeric.InfiniteIterationException;
import it.unive.lisa.util.numeric.IntInterval;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import it.unive.lisa.util.numeric.MathNumber;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.Test;

public class IntervalTest {

	private static final int TEST_LIMIT = 5000;

	private final Random rand = new Random();
	private final ProgramPoint pp = TestParameterProvider.provideParam(null, ProgramPoint.class);;
	private final Interval singleton = new Interval();
	private final Variable variable = new Variable(Int32Type.INSTANCE, "x", pp.getLocation());
	private final Variable varAux = new Variable(Int32Type.INSTANCE, "aux", pp.getLocation());
	private final ValueEnvironment<
			Interval> env = new ValueEnvironment<>(singleton).putState(variable, singleton.top());
	private final SemanticOracle oracle = TestParameterProvider.provideParam(null, SemanticOracle.class);

	@Test
	public void testEvalConstant() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			assertTrue("eval(" + val + ") did not return [" + val + ", " + val + "]",
					singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp,
									oracle).interval
							.is(val));
		}
	}

	@Test
	public void testEvalNegationOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			Interval aval = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp,
					oracle);
			assertTrue("eval(-" + val + ") did not return [-" + val + ", -" + val + "]",
					singleton.evalUnaryExpression(NumericNegation.INSTANCE, aval, pp, oracle).interval.is(-val));
		}
	}

	@Test
	public void testEvalAddOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			IntInterval exp = aval1.interval.plus(aval2.interval);
			assertEquals("eval(" + val1 + " + " + val2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingAdd.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testEvalSubOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			IntInterval exp = aval1.interval.diff(aval2.interval);
			assertEquals("eval(" + val1 + " - " + val2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingSub.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testEvalMulOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			IntInterval exp = aval1.interval.mul(aval2.interval);
			assertEquals("eval(" + val1 + " * " + val2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingMul.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testEvalDivOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			IntInterval exp = aval1.interval.div(aval2.interval, false, false);
			assertEquals("eval(" + val1 + " / " + val2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingDiv.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testLatticeOperationsOnSingleton() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Interval lub = aval1.lub(aval2);
			Interval widen = aval1.widening(aval2);
			Interval glb = aval1.glb(aval2);
			assertTrue(aval1 + " does not include " + aval1, aval1.lessOrEqual(aval1));
			assertTrue(aval2 + " does not include " + aval2, aval2.lessOrEqual(aval2));
			assertTrue(aval1 + " lub " + aval2 + " (" + lub + ") does not include " + aval1, aval1.lessOrEqual(lub));
			assertTrue(aval1 + " lub " + aval2 + " (" + lub + ") does not include " + aval2, aval2.lessOrEqual(lub));
			assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not include " + aval1,
					aval1.lessOrEqual(widen));
			assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not include " + aval2,
					aval2.lessOrEqual(widen));
			if (val2 < val1)
				assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not have its lower bound set to -Inf",
						widen.interval.lowIsMinusInfinity());
			else
				assertFalse(aval1 + " widening " + aval2 + " (" + widen + ") has its lower bound set to -Inf",
						widen.interval.lowIsMinusInfinity());
			if (val2 > val1)
				assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not have its higher bound set to +Inf",
						widen.interval.highIsPlusInfinity());
			else
				assertFalse(aval1 + " widening " + aval2 + " (" + widen + ") has its higher bound set to +Inf",
						widen.interval.highIsPlusInfinity());
			assertTrue(aval1 + " glb " + aval2 + " (" + glb + ") is not included in " + aval1, glb.lessOrEqual(aval1));
			assertTrue(aval1 + " glb " + aval2 + " (" + glb + ") is not included in " + aval2, glb.lessOrEqual(aval2));
		}
	}

	@Test
	public void testStatisfiesEQOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Satisfiability exp = Satisfiability.fromBoolean(val1 == val2);
			assertEquals("satisfies(" + val1 + " == " + val2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonEq.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesNEOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Satisfiability exp = Satisfiability.fromBoolean(val1 != val2);
			assertEquals("satisfies(" + val1 + " != " + val2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonNe.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesGTOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Satisfiability exp = Satisfiability.fromBoolean(val1 > val2);
			assertEquals("satisfies(" + val1 + " > " + val2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonGt.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesGEOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Satisfiability exp = Satisfiability.fromBoolean(val1 >= val2);
			assertEquals("satisfies(" + val1 + " >= " + val2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonGe.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesLTOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Satisfiability exp = Satisfiability.fromBoolean(val1 < val2);
			assertEquals("satisfies(" + val1 + " < " + val2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonLt.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesLEOnSingleton() {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()),
					pp, oracle);
			Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()),
					pp, oracle);
			Satisfiability exp = Satisfiability.fromBoolean(val1 <= val2);
			assertEquals("satisfies(" + val1 + " <= " + val2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonLe.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testAssumeEQOnSingleton() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			Interval aval = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp,
					oracle);
			ValueEnvironment<Interval> exp = env.putState(variable, aval);
			assertEquals("assume(" + variable + " == " + val + ") did not return " + exp, exp,
					singleton.assumeBinaryExpression(env, ComparisonEq.INSTANCE,
							variable, new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp, pp, oracle));
		}
	}

	@Test
	public void testAssumeGTOnSingleton() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			Interval aval = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val + 1, pp.getLocation()),
					pp, oracle);
			// val + 1, +inf
			aval = aval.widening(
					singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val + 2, pp.getLocation()), pp,
							oracle));
			ValueEnvironment<Interval> exp = env.putState(variable, aval);
			assertEquals("assume(" + variable + " > " + val + ") did not return " + exp, exp,
					singleton.assumeBinaryExpression(env, ComparisonGt.INSTANCE,
							variable, new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp, pp, oracle));
		}
	}

	@Test
	public void testAssumeGEOnSingleton() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			Interval aval = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp,
					oracle);
			// val, +inf
			aval = aval.widening(
					singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val + 2, pp.getLocation()), pp,
							oracle));
			ValueEnvironment<Interval> exp = env.putState(variable, aval);
			assertEquals("assume(" + variable + " >= " + val + ") did not return " + exp, exp,
					singleton.assumeBinaryExpression(env, ComparisonGe.INSTANCE,
							variable, new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp, pp, oracle));
		}
	}

	@Test
	public void testAssumeLTOnSingleton() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			Interval aval = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val - 1, pp.getLocation()),
					pp, oracle);
			// -inf, val - 1
			aval = aval.widening(
					singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val - 2, pp.getLocation()), pp,
							oracle));
			ValueEnvironment<Interval> exp = env.putState(variable, aval);
			assertEquals("assume(" + variable + " < " + val + ") did not return " + exp, exp,
					singleton.assumeBinaryExpression(env, ComparisonLt.INSTANCE,
							variable, new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp, pp, oracle));
		}
	}

	@Test
	public void testAssumeLEOnSingleton() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val = rand.nextInt();
			Interval aval = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp,
					oracle);
			// -inf, val
			aval = aval.widening(
					singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val - 2, pp.getLocation()), pp,
							oracle));
			ValueEnvironment<Interval> exp = env.putState(variable, aval);
			assertEquals("assume(" + variable + " <= " + val + ") did not return " + exp, exp,
					singleton.assumeBinaryExpression(env, ComparisonLe.INSTANCE,
							variable, new Constant(Int32Type.INSTANCE, val, pp.getLocation()), pp, pp, oracle));
		}
	}

	private Interval mk(
			int val1,
			int val2)
			throws SemanticException {
		Interval aval1 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val1, pp.getLocation()), pp,
				oracle);
		Interval aval2 = singleton.evalNonNullConstant(new Constant(Int32Type.INSTANCE, val2, pp.getLocation()), pp,
				oracle);
		return aval1.lub(aval2);
	}

	@Test
	public void testEvalNegation() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval = mk(val1, val2);
			Interval exp = mk(-val1, -val2);
			assertEquals("eval(-" + aval + ") did not return " + exp, exp,
					singleton.evalUnaryExpression(NumericNegation.INSTANCE, aval, pp, oracle));
		}
	}

	@Test
	public void testEvalAdd() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			IntInterval exp = aval1.interval.plus(aval2.interval);
			assertEquals("eval(" + aval1 + " + " + aval2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingAdd.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testEvalSub() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			IntInterval exp = aval1.interval.diff(aval2.interval);
			assertEquals("eval(" + aval1 + " - " + aval2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingSub.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testEvalMul() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			IntInterval exp = aval1.interval.mul(aval2.interval);
			assertEquals("eval(" + aval1 + " * " + aval2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingMul.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testEvalDiv() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			IntInterval exp = aval1.interval.div(aval2.interval, false, false);
			assertEquals("eval(" + aval1 + " / " + aval2 + ") did not return " + exp, exp,
					singleton.evalBinaryExpression(NumericNonOverflowingDiv.INSTANCE, aval1, aval2,
							pp, oracle).interval);
		}
	}

	@Test
	public void testLatticeOperations() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Interval lub = aval1.lub(aval2);
			Interval widen = aval1.widening(aval2);
			Interval glb = aval1.glb(aval2);
			assertTrue(aval1 + " does not include " + aval1, aval1.lessOrEqual(aval1));
			assertTrue(aval2 + " does not include " + aval2, aval2.lessOrEqual(aval2));
			assertTrue(aval1 + " lub " + aval2 + " (" + lub + ") does not include " + aval1, aval1.lessOrEqual(lub));
			assertTrue(aval1 + " lub " + aval2 + " (" + lub + ") does not include " + aval2, aval2.lessOrEqual(lub));
			assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not include " + aval1,
					aval1.lessOrEqual(widen));
			assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not include " + aval2,
					aval2.lessOrEqual(widen));
			if (aval2.interval.getLow().compareTo(aval1.interval.getLow()) < 0)
				assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not have its lower bound set to -Inf",
						widen.interval.lowIsMinusInfinity());
			else
				assertEquals(
						aval1 + " widening " + aval2 + " (" + widen
								+ ") has its lower bound different from the original",
						aval1.interval.getLow(), widen.interval.getLow());
			if (aval2.interval.getHigh().compareTo(aval1.interval.getHigh()) > 0)
				assertTrue(aval1 + " widening " + aval2 + " (" + widen + ") does not have its higher bound set to +Inf",
						widen.interval.highIsPlusInfinity());
			else
				assertEquals(
						aval1 + " widening " + aval2 + " (" + widen
								+ ") has its higher bound different from the original",
						aval1.interval.getHigh(), widen.interval.getHigh());
			assertTrue(aval1 + " glb " + aval2 + " (" + glb + ") is not included in " + aval1, glb.lessOrEqual(aval1));
			assertTrue(aval1 + " glb " + aval2 + " (" + glb + ") is not included in " + aval2, glb.lessOrEqual(aval2));
		}
	}

	@Test
	public void testStatisfiesEQ() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Satisfiability exp = Satisfiability.fromBoolean(aval1.equals(aval2) && aval1.interval.isSingleton());
			exp = exp.lub(Satisfiability.fromBoolean(aval1.interval.intersects(aval2.interval)));
			assertEquals("satisfies(" + aval1 + " == " + aval2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonEq.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesNE() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Satisfiability exp = Satisfiability.fromBoolean(!aval1.interval.intersects(aval2.interval));
			if (exp == Satisfiability.NOT_SATISFIED)
				exp = Satisfiability.UNKNOWN;
			assertEquals("satisfies(" + aval1 + " != " + aval2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonNe.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesGT() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Satisfiability exp;
			if (aval1.interval.intersects(aval2.interval))
				exp = Satisfiability.UNKNOWN;
			else
				exp = Satisfiability.fromBoolean(aval1.interval.getLow().compareTo(aval2.interval.getHigh()) > 0);
			assertEquals("satisfies(" + aval1 + " > " + aval2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonGt.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesGE() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Satisfiability exp;
			if (aval1.interval.intersects(aval2.interval))
				exp = Satisfiability.UNKNOWN;
			else
				exp = Satisfiability.fromBoolean(aval1.interval.getLow().compareTo(aval2.interval.getHigh()) >= 0);
			assertEquals("satisfies(" + aval1 + " >= " + aval2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonGe.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesLT() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Satisfiability exp;
			if (aval1.interval.intersects(aval2.interval))
				exp = Satisfiability.UNKNOWN;
			else
				exp = Satisfiability.fromBoolean(aval1.interval.getLow().compareTo(aval2.interval.getHigh()) < 0);
			assertEquals("satisfies(" + aval1 + " < " + aval2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonLt.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testStatisfiesLE() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			int val3 = rand.nextInt();
			int val4 = rand.nextInt();
			Interval aval1 = mk(val1, val2);
			Interval aval2 = mk(val3, val4);
			Satisfiability exp;
			if (aval1.interval.intersects(aval2.interval))
				exp = Satisfiability.UNKNOWN;
			else
				exp = Satisfiability.fromBoolean(aval1.interval.getLow().compareTo(aval2.interval.getHigh()) <= 0);
			assertEquals("satisfies(" + aval1 + " <= " + aval2 + ") did not return " + exp, exp,
					singleton.satisfiesBinaryExpression(ComparisonLe.INSTANCE, aval1, aval2, pp, oracle));
		}
	}

	@Test
	public void testAssumeEQ() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval aval = mk(val1, val2);
			ValueEnvironment<Interval> start = env.putState(varAux, aval);
			ValueEnvironment<Interval> exp = start.putState(variable, aval);
			assertEquals("assume(" + variable + " == " + aval + ") did not return " + exp, exp,
					singleton.assumeBinaryExpression(start, ComparisonEq.INSTANCE,
							variable, varAux, pp, pp, oracle));
		}
	}

	@Test
	public void testAssumeGT() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval bound = mk(val1, val2);
			// low + 1, +inf
			Interval aval = val1 < val2 ? mk(val1 + 1, val2) : mk(val1, val2 + 1);
			aval = aval.widening(mk(val1 + 1, val2 + 1));
			ValueEnvironment<Interval> start = env.putState(varAux, bound);
			ValueEnvironment<Interval> exp = start.putState(variable, aval);
			ValueEnvironment<Interval> act = singleton.assumeBinaryExpression(start, ComparisonGt.INSTANCE,
					variable, varAux, pp, pp, oracle);
			assertEquals("assume(" + variable + " > " + bound + ") did not return " + exp, exp, act);
		}
	}

	@Test
	public void testAssumeGE() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval bound = mk(val1, val2);
			// low, +inf
			Interval aval = bound.widening(val1 < val2 ? mk(val1, val2 + 1) : mk(val1 + 1, val2));
			ValueEnvironment<Interval> start = env.putState(varAux, bound);
			ValueEnvironment<Interval> exp = start.putState(variable, aval);
			ValueEnvironment<Interval> act = singleton.assumeBinaryExpression(start, ComparisonGe.INSTANCE,
					variable, varAux, pp, pp, oracle);
			assertEquals("assume(" + variable + " >= " + bound + ") did not return " + exp, exp, act);
		}
	}

	@Test
	public void testAssumeLT() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval bound = mk(val1, val2);
			// -inf, high - 1
			Interval aval = val1 < val2 ? mk(val1, val2 - 1) : mk(val1 - 1, val2);
			aval = aval.widening(mk(val1 - 1, val2 - 1));
			ValueEnvironment<Interval> start = env.putState(varAux, bound);
			ValueEnvironment<Interval> exp = start.putState(variable, aval);
			ValueEnvironment<Interval> act = singleton.assumeBinaryExpression(start, ComparisonLt.INSTANCE,
					variable, varAux, pp, pp, oracle);
			assertEquals("assume(" + variable + " < " + bound + ") did not return " + exp, exp, act);
		}
	}

	@Test
	public void testAssumeLE() throws SemanticException {
		for (int i = 0; i < TEST_LIMIT; i++) {
			int val1 = rand.nextInt();
			int val2 = rand.nextInt();
			Interval bound = mk(val1, val2);
			// -inf, high
			Interval aval = bound.widening(val1 < val2 ? mk(val1 - 1, val2) : mk(val1, val2 - 1));
			ValueEnvironment<Interval> start = env.putState(varAux, bound);
			ValueEnvironment<Interval> exp = start.putState(variable, aval);
			ValueEnvironment<Interval> act = singleton.assumeBinaryExpression(start, ComparisonLe.INSTANCE,
					variable, varAux, pp, pp, oracle);
			assertEquals("assume(" + variable + " <= " + bound + ") did not return " + exp, exp, act);
		}
	}

	@Test(expected = InfiniteIterationException.class)
	public void testIteratorOnTopInterval() {
		Interval top = new Interval();

		for (Long l : top.interval)
			System.out.println(l);
	}

	@Test
	public void testIterator() throws SemanticException {
		Interval top = mk(-1, 2);
		List<Long> values = new ArrayList<>();
		for (Long l : top.interval)
			values.add(l);

		List<Long> expected = new ArrayList<>();
		expected.add((long) -1);
		expected.add((long) 0);
		expected.add((long) 1);
		expected.add((long) 2);
		assertEquals(values, expected);

	}

	@Test
	public void testSplitOnInterval() throws SemanticException {
		Variable x = new Variable(Int32Type.INSTANCE, "x", pp.getLocation());
		Variable c = new Variable(Int32Type.INSTANCE, "c", pp.getLocation());

		for(int i = 0; i < TEST_LIMIT; i++) {
			BinaryExpression eqExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonEq.INSTANCE, pp.getLocation());
			BinaryExpression neExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonNe.INSTANCE, pp.getLocation());
			BinaryExpression gtExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonGt.INSTANCE, pp.getLocation());
			BinaryExpression ltExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonLt.INSTANCE, pp.getLocation());
			BinaryExpression geExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonGe.INSTANCE, pp.getLocation());
			BinaryExpression leExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonLe.INSTANCE, pp.getLocation());

			Interval intervalToSplit = mk(rand.nextInt(TEST_LIMIT) + 1, rand.nextInt(TEST_LIMIT) + 1);

			int randInt = rand.nextInt(TEST_LIMIT) + 1;
			Interval randInterval = mk(randInt, randInt);

			ValueEnvironment<Interval> xEnvironment = new ValueEnvironment<>(intervalToSplit).putState(x, intervalToSplit);
			ValueEnvironment<Interval> cEnvironment = xEnvironment.putState(c, randInterval);

			MathNumber constantNumber = randInterval.interval.getHigh();
			MathNumber identifierLowNumber = intervalToSplit.interval.getLow();
			MathNumber identifierHighNumber = intervalToSplit.interval.getHigh();

			Pair<Interval, Interval> expEqualCase = null;
			Pair<Interval, Interval> expNotEqualCase = null;
			Pair<Interval, Interval> expGreaterThanCase = null;
			Pair<Interval, Interval> expLessThanCase = null;
			Pair<Interval, Interval> expGreaterOrEqualCase = null;
			Pair<Interval, Interval> expLessOrEqualCase = null;
			if(constantNumber.lt(identifierLowNumber)) {
				expEqualCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expNotEqualCase = Pair.of(intervalToSplit, new Interval().bottom());
				expGreaterThanCase = Pair.of(intervalToSplit, new Interval().bottom());
				expLessThanCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expGreaterOrEqualCase = Pair.of(intervalToSplit, new Interval().bottom());
				expLessOrEqualCase = Pair.of(new Interval().bottom(), intervalToSplit);
			} else if(constantNumber.gt(identifierHighNumber)) {
				expEqualCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expNotEqualCase = Pair.of(intervalToSplit, new Interval().bottom());
				expGreaterThanCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expLessThanCase = Pair.of(intervalToSplit, new Interval().bottom());
				expGreaterOrEqualCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expLessOrEqualCase = Pair.of(intervalToSplit, new Interval().bottom());
			} else if(constantNumber.equals(identifierHighNumber)) {
				expEqualCase = Pair.of(randInterval, new Interval(intervalToSplit.interval.getLow(), intervalToSplit.interval.getHigh()));
				expNotEqualCase = Pair.of(new Interval(intervalToSplit.interval.getLow(), intervalToSplit.interval.getHigh()), randInterval);
				expGreaterThanCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expLessOrEqualCase = Pair.of(intervalToSplit, new Interval().bottom());
				expGreaterOrEqualCase = Pair.of(new Interval(randInterval.interval.getLow(), intervalToSplit.interval.getHigh()),
						new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getLow().subtract(MathNumber.ONE)));
				expLessThanCase = Pair.of(new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getHigh().subtract(MathNumber.ONE)),
						new Interval(randInterval.interval.getLow(), intervalToSplit.interval.getHigh()));
			} else if(constantNumber.equals(identifierLowNumber)) {
				expEqualCase = Pair.of(randInterval, new Interval(intervalToSplit.interval.getLow(), intervalToSplit.interval.getHigh()));
				expNotEqualCase = Pair.of(new Interval(intervalToSplit.interval.getLow(), intervalToSplit.interval.getHigh()), randInterval);
				expLessThanCase = Pair.of(new Interval().bottom(), intervalToSplit);
				expGreaterOrEqualCase = Pair.of(intervalToSplit, new Interval().bottom());
				expGreaterThanCase = Pair.of(new Interval(randInterval.interval.getHigh().add(MathNumber.ONE), intervalToSplit.interval.getHigh()),
						new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getHigh()));
				expLessOrEqualCase = Pair.of(new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getHigh()),
						new Interval(randInterval.interval.getHigh().add(MathNumber.ONE), intervalToSplit.interval.getHigh()));
			} else {
				expEqualCase = Pair.of(randInterval, intervalToSplit);
				expNotEqualCase = Pair.of(intervalToSplit, randInterval);
				expGreaterThanCase = Pair.of(new Interval(randInterval.interval.getHigh().add(MathNumber.ONE), intervalToSplit.interval.getHigh()),
						new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getHigh()));
				expLessThanCase = Pair.of(new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getHigh().subtract(MathNumber.ONE)),
						new Interval(randInterval.interval.getLow(), intervalToSplit.interval.getHigh()));
				expGreaterOrEqualCase = Pair.of(new Interval(randInterval.interval.getLow(), intervalToSplit.interval.getHigh()),
						new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getLow().subtract(MathNumber.ONE)));
				expLessOrEqualCase = Pair.of(new Interval(intervalToSplit.interval.getLow(), randInterval.interval.getHigh()),
						new Interval(randInterval.interval.getHigh().add(MathNumber.ONE), intervalToSplit.interval.getHigh()));
			}

			System.out.println("------------------------------------------ inizio iter: " + i + " -----------------------------");
			System.out.println("x environment: " + xEnvironment);
			System.out.println("c environment: " + cEnvironment);
			System.out.println("-----------------------------------------------------------------------------------------------");
			System.out.println("x: " + intervalToSplit + ", c: " + randInterval);
			System.out.println("expression: " + eqExpr);
			Pair<Interval, Interval> actualEqualCase = intervalToSplit.split(cEnvironment, eqExpr, pp, pp, oracle);
			System.out.println("Operator (==), Expected: " + expEqualCase + ", Actual: " + actualEqualCase);
			System.out.println("-----------------------------------------------------------------------------------------------");
			System.out.println("x: " + intervalToSplit + ", c: " + randInterval);
			System.out.println("expression: " + neExpr);
			Pair<Interval, Interval> actualNotEqualCase = intervalToSplit.split(cEnvironment, neExpr, pp, pp, oracle);
			System.out.println("Operator (!=), Expected: " + expNotEqualCase + ", Actual: " + actualNotEqualCase);
			System.out.println("-----------------------------------------------------------------------------------------------");
			System.out.println("x: " + intervalToSplit + ", c: " + randInterval);
			System.out.println("expression: " + gtExpr);
			Pair<Interval, Interval> actualGreaterThanCase = intervalToSplit.split(cEnvironment, gtExpr, pp, pp, oracle);
			System.out.println("Operator  (>), Expected: " + expGreaterThanCase + ", Actual: " + actualGreaterThanCase);
			System.out.println("-----------------------------------------------------------------------------------------------");
			System.out.println("x: " + intervalToSplit + ", c: " + randInterval);
			System.out.println("expression: " + ltExpr);
			Pair<Interval, Interval> actualLessThanCase = intervalToSplit.split(cEnvironment, ltExpr, pp, pp, oracle);
			System.out.println("Operator  (<), Expected: " + expLessThanCase + ", Actual: " + actualLessThanCase);
			System.out.println("-----------------------------------------------------------------------------------------------");
			System.out.println("x: " + intervalToSplit + ", c: " + randInterval);
			System.out.println("expression: " + geExpr);
			Pair<Interval, Interval> actualGreaterOrEqualCase = intervalToSplit.split(cEnvironment, geExpr, pp, pp, oracle);
			System.out.println("Operator (>=), Expected: " + expGreaterOrEqualCase + ", Actual: " + actualGreaterOrEqualCase);
			System.out.println("-----------------------------------------------------------------------------------------------");
			System.out.println("x: " + intervalToSplit + ", c: " + randInterval);
			System.out.println("expression: " + leExpr);
			Pair<Interval, Interval> actualLessOrEqualCase = intervalToSplit.split(cEnvironment, leExpr, pp, pp, oracle);
			System.out.println("Operator (<=), Expected: " + expLessOrEqualCase + ", Actual: " + actualLessOrEqualCase);
			System.out.println("---------------------------------------------- fine iter: " + i + "----------------------------");

			assertEquals("The values don't match for equal operator: ", expEqualCase, actualEqualCase);
			assertEquals("The values don't match for not equal operator: ", expNotEqualCase, actualNotEqualCase);
			assertEquals("The values don't match for greater than operator: ", expGreaterThanCase, actualGreaterThanCase);
			assertEquals("The values don't match for less than operator: ", expLessThanCase, actualLessThanCase);
			assertEquals("The values don't match for greater or equal than operator: ", expGreaterOrEqualCase, actualGreaterOrEqualCase);
			assertEquals("The values don't match for less or equal than operator: ", expLessOrEqualCase, actualLessOrEqualCase);
		}
	}
}
