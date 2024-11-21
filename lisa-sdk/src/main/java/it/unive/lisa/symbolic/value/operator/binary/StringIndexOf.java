package it.unive.lisa.symbolic.value.operator.binary;

import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.type.NumericType;
import it.unive.lisa.type.StringType;
import it.unive.lisa.type.Type;
import it.unive.lisa.type.TypeSystem;

/**
 * Given two expressions that both evaluate to string values, a
 * {@link BinaryExpression} using this operator computes the starting index
 * <i>of the first occurrence</i> of the string from the second argument inside
 * the one of the first argument, producing {@code -1} if no occurrence can be
 * found.<br>
 * <br>
 * First argument expression type: {@link StringType}<br>
 * Second argument expression type: {@link StringType}<br>
 * Computed expression type: {@link NumericType} (integral)
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class StringIndexOf extends StringOperation {

	/**
	 * The singleton instance of this class.
	 */
	public static final StringIndexOf INSTANCE = new StringIndexOf();

	/**
	 * Builds the operator. This constructor is visible to allow subclassing:
	 * instances of this class should be unique, and the singleton can be
	 * retrieved through field {@link #INSTANCE}.
	 */
	protected StringIndexOf() {
	}

	@Override
	public String toString() {
		return "strindexof";
	}

	@Override
	protected Type resultType(
			TypeSystem types) {
		return types.getIntegerType();
	}
}
