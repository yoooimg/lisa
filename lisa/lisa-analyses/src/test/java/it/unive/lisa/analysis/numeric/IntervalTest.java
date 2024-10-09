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
	private final ProgramPoint pp = TestParameterProvider.provideParam(null, ProgramPoint.class);
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
		for (int i = 0; i < TEST_LIMIT; i++) {
			BinaryExpression eqExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonEq.INSTANCE, pp.getLocation());
			BinaryExpression neExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonNe.INSTANCE, pp.getLocation());
			BinaryExpression gtExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonGt.INSTANCE, pp.getLocation());
			BinaryExpression ltExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonLt.INSTANCE, pp.getLocation());
			BinaryExpression geExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonGe.INSTANCE, pp.getLocation());
			BinaryExpression leExpr = new BinaryExpression(Int32Type.INSTANCE, x, c, ComparisonLe.INSTANCE, pp.getLocation());

			Interval xInterval = mk(rand.nextInt(3) + 1, rand.nextInt(3) + 1);
			int randInt = rand.nextInt(3) + 1;
			Interval cInterval = mk(randInt, randInt);
			ValueEnvironment<Interval> environment = new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval);

			MathNumber constantNumber = cInterval.interval.getHigh();
			MathNumber low = xInterval.interval.getLow();
			MathNumber high = xInterval.interval.getHigh();

			System.out.println("********************(==)********************");
			System.out.println("expression: " + eqExpr);
			System.out.println("x interval: " + xInterval + ", c interval: " + cInterval);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> actualEqEnvs = xInterval.split(environment, eqExpr, pp, pp, oracle);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> expectedEqEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, cInterval).putState(c, cInterval),
					new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval));
			System.out.println("actual envs: " + actualEqEnvs);
			System.out.println("expected envs: " + expectedEqEnvs);
			assertEquals("The values don't match: ", actualEqEnvs, expectedEqEnvs);
			System.out.println("*******************************************");

			System.out.println("*********************(!=)*******************");
			System.out.println("expression: " + neExpr);
			System.out.println("x interval: " + xInterval + ", c interval: " + cInterval);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> actualNeEnvs = xInterval.split(environment, neExpr, pp, pp, oracle);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> expectedNeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval)
					, new ValueEnvironment<>(xInterval).putState(x, cInterval).putState(c, cInterval));
			System.out.println("actual envs: " + actualNeEnvs);
			System.out.println("expected envs: " + expectedNeEnvs);
			assertEquals("The values don't match: ", actualNeEnvs, expectedNeEnvs);
			System.out.println("********************************************");

			System.out.println("*********************(>)*******************");
			System.out.println("expression: " + gtExpr);
			System.out.println("x interval: " + xInterval + ", c interval: " + cInterval);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> actualGtEnvs = xInterval.split(environment, gtExpr, pp, pp, oracle);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> expectedGtEnvs = null;
			if (low.gt(constantNumber))
				expectedGtEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval),
						new ValueEnvironment<>(new Interval().bottom()));
			else if (high.leq(constantNumber)) {
				expectedGtEnvs = Pair.of(new ValueEnvironment<>(new Interval().bottom()),
						new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval));
			} else if (low.leq(constantNumber) && high.gt(constantNumber)) {
				expectedGtEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, new Interval(constantNumber.add(MathNumber.ONE), high)).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(low, constantNumber)).putState(c, cInterval));
			} else {
				expectedGtEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(low, constantNumber)).putState(c, cInterval));
			}
			System.out.println("actual envs: " + actualGtEnvs);
			System.out.println("expected envs: " + expectedGtEnvs);
			assertEquals("The values don't match: ", actualGtEnvs, expectedGtEnvs);
			System.out.println("********************************************");

			System.out.println("*********************(<)*******************");
			System.out.println("expression: " + ltExpr);
			System.out.println("x interval: " + xInterval + ", c interval: " + cInterval);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> actualLtEnvs = xInterval.split(environment, ltExpr, pp, pp, oracle);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> expectedLtEnvs = null;
			if (high.lt(constantNumber))
				expectedLtEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval),
						new ValueEnvironment<>(new Interval().bottom()));
			else if (low.lt(constantNumber) && high.geq(constantNumber)) {
				expectedLtEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, new Interval(low, constantNumber.subtract(MathNumber.ONE))).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(constantNumber, high)).putState(c, cInterval));
			} else if (high.geq(constantNumber)) {
				expectedLtEnvs = Pair.of(new ValueEnvironment<>(new Interval().bottom()),
						new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval));
			}
			System.out.println("actual envs: " + actualLtEnvs);
			System.out.println("expected envs: " + expectedLtEnvs);
			assertEquals("The values don't match: ", actualLtEnvs, expectedLtEnvs);
			System.out.println("********************************************");

			System.out.println("*********************(>=)*******************");
			System.out.println("expression: " + geExpr);
			System.out.println("x interval: " + xInterval + ", c interval: " + cInterval);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> actualGeEnvs = xInterval.split(environment, geExpr, pp, pp, oracle);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> expectedGeEnvs = null;

			if (constantNumber.leq(low) && constantNumber.lt(high))
				expectedGeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval),
						new ValueEnvironment<>(new Interval().bottom()));
			else if (high.lt(constantNumber)) {
				expectedGeEnvs = Pair.of(new ValueEnvironment<>(new Interval().bottom()),
						new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval));
			} else if (low.lt(constantNumber) && high.gt(constantNumber)) {
				expectedGeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, new Interval(constantNumber, high)).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(low, constantNumber.subtract(MathNumber.ONE))).putState(c, cInterval));
			} else if(low.lt(constantNumber) && high.equals(constantNumber)) {
				expectedGeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, cInterval).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(low, constantNumber.subtract(MathNumber.ONE))).putState(c, cInterval));
			} else if(constantNumber.equals(low) && constantNumber.equals(high)) {
				expectedGeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval),
						new ValueEnvironment<>(new Interval().bottom()));
			}
			System.out.println("actual envs: " + actualGeEnvs);
			System.out.println("expected envs: " + expectedGeEnvs);
			assertEquals("The values don't match: ", actualGeEnvs, expectedGeEnvs);
			System.out.println("********************************************");

			System.out.println("*********************(<=)*******************");
			System.out.println("expression: " + leExpr);
			System.out.println("x interval: " + xInterval + ", c interval: " + cInterval);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> actualLeEnvs = xInterval.split(environment, leExpr, pp, pp, oracle);
			Pair<ValueEnvironment<Interval>, ValueEnvironment<Interval>> expectedLeEnvs = null;

			if (low.gt(constantNumber) && high.gt(constantNumber))
				expectedLeEnvs = Pair.of(new ValueEnvironment<>(new Interval().bottom()),
						new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval));
			else if (low.lt(constantNumber) && high.gt(constantNumber)) {
				expectedLeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, new Interval(low, constantNumber)).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(constantNumber.add(MathNumber.ONE), high)).putState(c, cInterval));
			} else if (high.leq(constantNumber)) {
				expectedLeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, xInterval).putState(c, cInterval),
						new ValueEnvironment<>(new Interval().bottom()));
			} else if (low.leq(constantNumber) && high.gt(constantNumber)) {
				expectedLeEnvs = Pair.of(new ValueEnvironment<>(xInterval).putState(x, cInterval).putState(c, cInterval),
						new ValueEnvironment<>(xInterval).putState(x, new Interval(constantNumber.add(MathNumber.ONE), high)).putState(c, cInterval));
			}
			System.out.println("actual envs: " + actualLeEnvs);
			System.out.println("expected envs: " + expectedLeEnvs);
			assertEquals("The values don't match: ", actualLeEnvs, expectedLeEnvs);
			System.out.println("********************************************");
		}
	}
}
