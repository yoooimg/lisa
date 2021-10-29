package it.unive.lisa.symbolic.value;

import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.type.BooleanType;
import it.unive.lisa.type.NumericType;
import it.unive.lisa.type.StringType;
import it.unive.lisa.type.Type;
import it.unive.lisa.type.TypeTokenType;

/**
 * A binary {@link Operator} that can be applied to a pair of
 * {@link SymbolicExpression}s.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public enum BinaryOperator implements Operator {

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * subtraction of those values. This operation does never
	 * overflows/underflows.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	NUMERIC_NON_OVERFLOWING_SUB("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * subtraction of those values. Both arguments and results are expected to
	 * be 8-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (8-bit)<br>
	 * Second argument expression type: {@link NumericType} (8-bit)<br>
	 * Computed expression type: {@link NumericType} (8-bit)
	 */
	NUMERIC_8BIT_SUB("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * subtraction of those values. Both arguments and results are expected to
	 * be 16-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (16-bit)<br>
	 * Second argument expression type: {@link NumericType} (16-bit)<br>
	 * Computed expression type: {@link NumericType} (16-bit)
	 */
	NUMERIC_16BIT_SUB("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * subtraction of those values. Both arguments and results are expected to
	 * be 32-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (32-bit)<br>
	 * Second argument expression type: {@link NumericType} (32-bit)<br>
	 * Computed expression type: {@link NumericType} (32-bit)
	 */
	NUMERIC_32BIT_SUB("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * subtraction of those values. Both arguments and results are expected to
	 * be 64-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (64-bit)<br>
	 * Second argument expression type: {@link NumericType} (64-bit)<br>
	 * Computed expression type: {@link NumericType} (64-bit)
	 */
	NUMERIC_64BIT_SUB("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * addition of those values. This operation does never
	 * overflows/underflows.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	NUMERIC_NON_OVERFLOWING_ADD("+"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * addition of those values. Both arguments and results are expected to be
	 * 8-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (8-bit)<br>
	 * Second argument expression type: {@link NumericType} (8-bit)<br>
	 * Computed expression type: {@link NumericType} (8-bit)
	 */
	NUMERIC_8BIT_ADD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * addition of those values. Both arguments and results are expected to be
	 * 16-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (16-bit)<br>
	 * Second argument expression type: {@link NumericType} (16-bit)<br>
	 * Computed expression type: {@link NumericType} (16-bit)
	 */
	NUMERIC_16BIT_ADD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * addition of those values. Both arguments and results are expected to be
	 * 32-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (32-bit)<br>
	 * Second argument expression type: {@link NumericType} (32-bit)<br>
	 * Computed expression type: {@link NumericType} (32-bit)
	 */
	NUMERIC_32BIT_ADD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * addition of those values. Both arguments and results are expected to be
	 * 64-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (64-bit)<br>
	 * Second argument expression type: {@link NumericType} (64-bit)<br>
	 * Computed expression type: {@link NumericType} (64-bit)
	 */
	NUMERIC_64BIT_ADD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * division of those values. This operation does never
	 * overflows/underflows.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	NUMERIC_NON_OVERFLOWING_DIV("/"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * division of those values. Both arguments and results are expected to be
	 * 8-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (8-bit)<br>
	 * Second argument expression type: {@link NumericType} (8-bit)<br>
	 * Computed expression type: {@link NumericType} (8-bit)
	 */
	NUMERIC_8BIT_DIV("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * division of those values. Both arguments and results are expected to be
	 * 16-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (16-bit)<br>
	 * Second argument expression type: {@link NumericType} (16-bit)<br>
	 * Computed expression type: {@link NumericType} (16-bit)
	 */
	NUMERIC_16BIT_DIV("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * division of those values. Both arguments and results are expected to be
	 * 32-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (32-bit)<br>
	 * Second argument expression type: {@link NumericType} (32-bit)<br>
	 * Computed expression type: {@link NumericType} (32-bit)
	 */
	NUMERIC_32BIT_DIV("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * division of those values. Both arguments and results are expected to be
	 * 64-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (64-bit)<br>
	 * Second argument expression type: {@link NumericType} (64-bit)<br>
	 * Computed expression type: {@link NumericType} (64-bit)
	 */
	NUMERIC_64BIT_DIV("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * multiplication of those values. This operation does never
	 * overflows/underflows.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	NUMERIC_NON_OVERFLOWING_MUL("*"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * multiplication of those values. Both arguments and results are expected
	 * to be 8-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (8-bit)<br>
	 * Second argument expression type: {@link NumericType} (8-bit)<br>
	 * Computed expression type: {@link NumericType} (8-bit)
	 */
	NUMERIC_8BIT_MUL("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * multiplication of those values. Both arguments and results are expected
	 * to be 16-bits numbers, and this operation thus can
	 * overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (16-bit)<br>
	 * Second argument expression type: {@link NumericType} (16-bit)<br>
	 * Computed expression type: {@link NumericType} (16-bit)
	 */
	NUMERIC_16BIT_MUL("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * multiplication of those values. Both arguments and results are expected
	 * to be 32-bits numbers, and this operation thus can
	 * overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (32-bit)<br>
	 * Second argument expression type: {@link NumericType} (32-bit)<br>
	 * Computed expression type: {@link NumericType} (32-bit)
	 */
	NUMERIC_32BIT_MUL("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * multiplication of those values. Both arguments and results are expected
	 * to be 64-bits numbers, and this operation thus can
	 * overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (64-bit)<br>
	 * Second argument expression type: {@link NumericType} (64-bit)<br>
	 * Computed expression type: {@link NumericType} (64-bit)
	 */
	NUMERIC_64BIT_MUL("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * remainder of those values. This operation does never
	 * overflows/underflows.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	NUMERIC_NON_OVERFLOWING_MOD("%"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * remainder of those values. Both arguments and results are expected to be
	 * 8-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (8-bit)<br>
	 * Second argument expression type: {@link NumericType} (8-bit)<br>
	 * Computed expression type: {@link NumericType} (8-bit)
	 */
	NUMERIC_8BIT_MOD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * remainder of those values. Both arguments and results are expected to be
	 * 16-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (16-bit)<br>
	 * Second argument expression type: {@link NumericType} (16-bit)<br>
	 * Computed expression type: {@link NumericType} (16-bit)
	 */
	NUMERIC_16BIT_MOD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * remainder of those values. Both arguments and results are expected to be
	 * 32-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (32-bit)<br>
	 * Second argument expression type: {@link NumericType} (32-bit)<br>
	 * Computed expression type: {@link NumericType} (32-bit)
	 */
	NUMERIC_32BIT_MOD("-"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the arithmetic
	 * remainder of those values. Both arguments and results are expected to be
	 * 64-bits numbers, and this operation thus can overflow/underflow.<br>
	 * <br>
	 * First argument expression type: {@link NumericType} (64-bit)<br>
	 * Second argument expression type: {@link NumericType} (64-bit)<br>
	 * Computed expression type: {@link NumericType} (64-bit)
	 */
	NUMERIC_64BIT_MOD("-"),

	/**
	 * Given two expressions that both evaluate to Boolean values, a
	 * {@link BinaryExpression} using this operator computes the logical
	 * disjunction of those values, without short-circuiting.<br>
	 * <br>
	 * First argument expression type: {@link BooleanType}<br>
	 * Second argument expression type: {@link BooleanType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	LOGICAL_OR("||") {
		@Override
		public BinaryOperator opposite() {
			return LOGICAL_AND;
		}
	},

	/**
	 * Given two expressions that both evaluate to Boolean values, a
	 * {@link BinaryExpression} using this operator computes the logical
	 * conjunction of those values, without short-circuiting.<br>
	 * <br>
	 * First argument expression type: {@link BooleanType}<br>
	 * Second argument expression type: {@link BooleanType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	LOGICAL_AND("&&") {
		@Override
		public BinaryOperator opposite() {
			return LOGICAL_OR;
		}
	},

	/**
	 * Given two expressions, a {@link BinaryExpression} using this operator
	 * checks if the values those expressions compute to are different. This
	 * operator corresponds to the logical negation of
	 * {@link #COMPARISON_EQ}.<br>
	 * <br>
	 * First argument expression type: any {@link Type}<br>
	 * Second argument expression type: any {@link Type}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	COMPARISON_NE("!=") {
		@Override
		public BinaryOperator opposite() {
			return COMPARISON_EQ;
		}
	},

	/**
	 * Given two expressions, a {@link BinaryExpression} using this operator
	 * checks if the values those expressions compute to are different. This
	 * operator corresponds to the logical negation of
	 * {@link #COMPARISON_NE}.<br>
	 * <br>
	 * First argument expression type: any {@link Type}<br>
	 * Second argument expression type: any {@link Type}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	COMPARISON_EQ("==") {
		@Override
		public BinaryOperator opposite() {
			return COMPARISON_NE;
		}
	},

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator checks if the value of the
	 * first argument is greater or equal than the value of the right-hand
	 * side.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	COMPARISON_GE(">=") {
		@Override
		public BinaryOperator opposite() {
			return COMPARISON_LT;
		}
	},

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator checks if the value of the
	 * first argument is greater than the value of the second argument.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	COMPARISON_GT(">") {
		@Override
		public BinaryOperator opposite() {
			return COMPARISON_LE;
		}
	},

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator checks if the value of the
	 * first argument is less or equal than the value of the right-hand
	 * side.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	COMPARISON_LE("<=") {
		@Override
		public BinaryOperator opposite() {
			return COMPARISON_GT;
		}
	},

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator checks if the value of the
	 * first argument is less than the value of the second argument.<br>
	 * <br>
	 * First argument expression type: {@link NumericType}<br>
	 * Second argument expression type: {@link NumericType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	COMPARISON_LT("<") {
		@Override
		public BinaryOperator opposite() {
			return COMPARISON_GE;
		}
	},

	/**
	 * Given two expressions that both evaluate to string values, a
	 * {@link BinaryExpression} using this operator computes the concatenation
	 * of the string from the first argument with the one of the second
	 * argument.<br>
	 * <br>
	 * First argument expression type: {@link StringType}<br>
	 * Second argument expression type: {@link StringType}<br>
	 * Computed expression type: {@link StringType}
	 */
	STRING_CONCAT("strcat"),

	/**
	 * Given two expressions that both evaluate to string values, a
	 * {@link BinaryExpression} using this operator checks if the string from
	 * the first argument contains the one of the second argument.<br>
	 * <br>
	 * First argument expression type: {@link StringType}<br>
	 * Second argument expression type: {@link StringType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	STRING_CONTAINS("strcontains"),

	/**
	 * Given two expressions that both evaluate to string values, a
	 * {@link BinaryExpression} using this operator checks if the string from
	 * the first argument is prefixed by the one of the second argument.<br>
	 * <br>
	 * First argument expression type: {@link StringType}<br>
	 * Second argument expression type: {@link StringType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	STRING_STARTS_WITH("strstarts"),

	/**
	 * Given two expressions that both evaluate to string values, a
	 * {@link BinaryExpression} using this operator checks if the string from
	 * the first argument is suffixed by the one of the second argument.<br>
	 * <br>
	 * First argument expression type: {@link StringType}<br>
	 * Second argument expression type: {@link StringType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	STRING_ENDS_WITH("strends"),

	/**
	 * Given two expressions that both evaluate to string values, a
	 * {@link BinaryExpression} using this operator computes the starting index
	 * <i>of the first occurrence</i> of the string from the second argument
	 * inside the one of the first argument, producing {@code -1} if no
	 * occurrence can be found.<br>
	 * <br>
	 * First argument expression type: {@link StringType}<br>
	 * Second argument expression type: {@link StringType}<br>
	 * Computed expression type: {@link NumericType} (integral)
	 */
	STRING_INDEX_OF("strindexof"),

	/**
	 * Given two expressions that both evaluate to string values, a
	 * {@link BinaryExpression} using this operator checks if the string from
	 * the first argument is equal (in terms of contents, that is different from
	 * {@link #COMPARISON_EQ}) to the one of the second argument.<br>
	 * <br>
	 * First argument expression type: {@link StringType}<br>
	 * Second argument expression type: {@link StringType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	STRING_EQUALS("strcmp"),

	/**
	 * Given two expressions, with the second one evaluating to a type token, a
	 * {@link BinaryExpression} using this operator casts the type of the first
	 * argument to the type of the second argument. The resulting value is
	 * exactly the first argument, but with its runtime types <i>filtered</i> to
	 * be instances of the right-hand side type. Indeed, this operation on types
	 * is a narrowing operator, that is, the destination type is smaller than
	 * the source type.<br>
	 * This operator resembles the Java cast operation between reference types:
	 * when an object is cast to another type, its runtime types do not change,
	 * but the cast fails of the runtime type of the object is not a subtype of
	 * the desired type.<br>
	 * <br>
	 * First argument expression type: any {@link Type}<br>
	 * Second argument expression type: {@link TypeTokenType}<br>
	 * Computed expression type: first argument {@link Type}s filtered
	 */
	TYPE_CAST("cast-as"),

	/**
	 * Given two expressions, with the second one evaluating to a type token, a
	 * {@link BinaryExpression} using this operator converts the type of the
	 * first argument to the type of the second argument. The resulting value is
	 * exactly the first argument, but with its runtime types <i>changed</i> to
	 * be instances of the right-hand side type. Indeed, this operation on types
	 * is a widening operator, that is, the destination type is greater than the
	 * source type.<br>
	 * This operator resembles the Java cast operation between primitive types:
	 * when, for instance, an int is cast to a float, its runtime types does
	 * change, possibly with loss of information during the conversion.<br>
	 * <br>
	 * First argument expression type: any {@link Type}<br>
	 * Second argument expression type: {@link TypeTokenType}<br>
	 * Computed expression type: second argument inner {@link Type}s
	 */
	TYPE_CONV("conv-as"),

	/**
	 * Given two expressions, with the second one evaluating to a type token, a
	 * {@link BinaryExpression} using this operator checks if the runtime types
	 * of the value the first argument evaluates to are subtypes of the ones
	 * contained in the token.<br>
	 * <br>
	 * First argument expression type: any {@link Type}<br>
	 * Second argument expression type: {@link TypeTokenType}<br>
	 * Computed expression type: {@link BooleanType}
	 */
	TYPE_CHECK("is"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the AND operation
	 * (i.e., setting each bit to {@code 1} only if the corresponding bits of
	 * both operands are {@code 1}) on the arguments.<br>
	 * <br>
	 * First argument expression type: any {@link NumericType}<br>
	 * Second argument expression type: any {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	BITWISE_AND("&"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the OR operation
	 * (i.e., setting each bit to {@code 1} only if at least one of the
	 * corresponding bits of the operands are {@code 1}) on the arguments.<br>
	 * <br>
	 * First argument expression type: any {@link NumericType}<br>
	 * Second argument expression type: any {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	BITWISE_OR("|"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes the XOR operation
	 * (i.e., setting each bit to {@code 1} only the corresponding bits of the
	 * operands are different) on the arguments.<br>
	 * <br>
	 * First argument expression type: any {@link NumericType}<br>
	 * Second argument expression type: any {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	BITWISE_XOR("^"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes a new number built
	 * with the bits of the first argument's value shifted to the left by an
	 * amount specified by the second argument's value. Excess bits on the left
	 * are dropped, while new bits on the right are set to {@code 0}.<br>
	 * <br>
	 * First argument expression type: any {@link NumericType}<br>
	 * Second argument expression type: any {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	BITWISE_SHIFT_LEFT("<<"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes a new number built
	 * with the bits of the first argument's value shifted to the right by an
	 * amount specified by the second argument's value. Excess bits on the right
	 * are dropped, while new bits on the left preserve the sign of the original
	 * first argument's value: if it was negative, bits are set to {@code 1},
	 * otherwise they are set to {@code 0}.<br>
	 * <br>
	 * First argument expression type: any {@link NumericType}<br>
	 * Second argument expression type: any {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	BITWISE_SHIFT_RIGHT(">>"),

	/**
	 * Given two expressions that both evaluate to numeric values, a
	 * {@link BinaryExpression} using this operator computes a new number built
	 * with the bits of the first argument's value shifted to the right by an
	 * amount specified by the second argument's value. Excess bits on the right
	 * are dropped, while new bits on the left are set to {@code 0}.<br>
	 * <br>
	 * First argument expression type: any {@link NumericType}<br>
	 * Second argument expression type: any {@link NumericType}<br>
	 * Computed expression type: {@link NumericType}
	 */
	BITWISE_UNSIGNED_SHIFT_RIGHT(">>>");

	private final String representation;

	private BinaryOperator(String representation) {
		this.representation = representation;
	}

	@Override
	public String getStringRepresentation() {
		return representation;
	}

	@Override
	public String toString() {
		return getStringRepresentation();
	}
}