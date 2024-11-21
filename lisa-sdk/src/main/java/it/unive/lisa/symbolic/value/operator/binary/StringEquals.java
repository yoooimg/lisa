package it.unive.lisa.symbolic.value.operator.binary;

import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.type.BooleanType;
import it.unive.lisa.type.StringType;
import it.unive.lisa.type.Type;
import it.unive.lisa.type.TypeSystem;

/**
 * Given two expressions that both evaluate to string values, a
 * {@link BinaryExpression} using this operator checks if the string from the
 * first argument is equal (in terms of contents, that is different from
 * {@link ComparisonEq}) to the one of the second argument.<br>
 * <br>
 * First argument expression type: {@link StringType}<br>
 * Second argument expression type: {@link StringType}<br>
 * Computed expression type: {@link BooleanType}
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class StringEquals extends StringOperation {

	/**
	 * The singleton instance of this class.
	 */
	public static final StringEquals INSTANCE = new StringEquals();

	/**
	 * Builds the operator. This constructor is visible to allow subclassing:
	 * instances of this class should be unique, and the singleton can be
	 * retrieved through field {@link #INSTANCE}.
	 */
	protected StringEquals() {
	}

	@Override
	public String toString() {
		return "strcmp";
	}

	@Override
	protected Type resultType(
			TypeSystem types) {
		return types.getBooleanType();
	}
}
