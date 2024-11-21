package it.unive.lisa.type;

/**
 * Array type interface.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public interface ArrayType extends InMemoryType {

	/**
	 * Yields the type of the inner dimension of this array type. For instance,
	 * if this type represents {@code int[]}, this method will return
	 * {@code int}. Instead, if this type represents {@code int[][]}, this
	 * method will return {@code int[]}.
	 * 
	 * @return the inner type of this array type
	 */
	Type getInnerType();

	/**
	 * Yields the base type of this array type. For instance, if this type
	 * represents {@code int[]}, this method will return {@code int}. This is
	 * the case also this type represents {@code int[][]}.
	 * 
	 * @return the base type of this array type
	 */
	Type getBaseType();

	/**
	 * Yields the dimensions of this array type. For instance, if this type
	 * represents {@code int[]}, this method will return {@code 1}. Instead, if
	 * this type represents {@code int[][]}, this method will return {@code 2}.
	 * 
	 * @return the dimensions of this array type
	 */
	int getDimensions();
}
