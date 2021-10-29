package it.unive.lisa.type;

/**
 * Numeric type interface. Any concrete numerical type or numerical
 * sub-interface should implement/extend this interface.
 * 
 * @author <a href="mailto:vincenzo.arceri@unive.it">Vincenzo Arceri</a>
 */
public interface NumericType extends Type {

	/**
	 * Returns {@code true} if this numeric type follows a 8-bits format
	 * representation.
	 * 
	 * @return {@code true} if this numeric type follows a 8-bits format
	 *             representation; {@code false} otherwise
	 */
	boolean is8Bits();

	/**
	 * Returns {@code true} if this numeric type follows a 16-bits format
	 * representation.
	 * 
	 * @return {@code true} if this numeric type follows a 16-bits format
	 *             representation; {@code false} otherwise
	 */
	boolean is16Bits();

	/**
	 * Returns {@code true} if this numeric type follows a 32-bits format
	 * representation.
	 * 
	 * @return {@code true} if this numeric type follows a 32-bits format
	 *             representation; {@code false} otherwise
	 */
	boolean is32Bits();

	/**
	 * Returns {@code true} if this numeric type follows a 64-bits format
	 * representation.
	 * 
	 * @return {@code true} if this numeric type follows a 64-bits format
	 *             representation; {@code false} otherwise
	 */
	boolean is64Bits();

	/**
	 * Returns {@code true} if this numeric type is unsigned.
	 * 
	 * @return {@code true} if this numeric type is unsigned; {@code false}
	 *             otherwise
	 */
	boolean isUnsigned();

	/**
	 * Returns {@code true} if this numeric type is integral, representing one
	 * of the numbers in the mathematical set Z.
	 * 
	 * @return {@code true} if this numeric type is integral; {@code false}
	 *             otherwise
	 */
	boolean isIntegral();

	/**
	 * Returns {@code true} if this numeric type is signed.
	 * 
	 * @return {@code true} if this numeric type is signed; {@code false}
	 *             otherwise
	 */
	default boolean isSigned() {
		return !isUnsigned();
	}

	/**
	 * Checks if two implementations of {@link NumericType} represent the same
	 * type, and can thus be used interchangeably. For two instances represent
	 * the same type, every {@code isX} method defined by this interface has to
	 * return the same value.
	 * 
	 * @param t1 the first type
	 * @param t2 the second type
	 * 
	 * @return whether or not the two instances represent the same type
	 */
	public static boolean sameNumericTypes(NumericType t1, NumericType t2) {
		if (t1.is8Bits() != t2.is8Bits())
			return false;
		if (t1.is16Bits() != t2.is16Bits())
			return false;
		if (t1.is32Bits() != t2.is32Bits())
			return false;
		if (t1.is64Bits() != t2.is64Bits())
			return false;
		if (t1.isIntegral() != t2.isIntegral())
			return false;
		if (t1.isUnsigned() != t2.isUnsigned())
			return false;
		return true;
	}

	/**
	 * Determines which of the two {@link NumericType}s is supertype for the
	 * other. At first, the size of the two types is considered, and the larger
	 * size takes precedence. Then, precedence is given to non-integral types,
	 * and at last, to signed types.
	 * 
	 * @param t1 the first type
	 * @param t2 the second type
	 * 
	 * @return the supertype between the two
	 */
	public static NumericType supertype(NumericType t1, NumericType t2) {
		if (t1.is8Bits() && (t2.is16Bits() || t2.is32Bits() || t2.is64Bits()))
			return t2;
		if (t2.is8Bits() && (t1.is16Bits() || t1.is32Bits() || t1.is64Bits()))
			return t1;

		if (t1.is16Bits() && (t2.is32Bits() || t2.is64Bits()))
			return t2;
		if (t2.is16Bits() && (t1.is32Bits() || t1.is64Bits()))
			return t1;

		if (t1.is32Bits() && t2.is64Bits())
			return t2;
		if (t2.is32Bits() && t1.is64Bits())
			return t1;

		// both 64 bits

		if (t1.isIntegral() && !t2.isIntegral())
			return t2;
		if (!t1.isIntegral() && t2.isIntegral())
			return t1;

		if (t1.isUnsigned() && t2.isSigned())
			return t2;
		if (t1.isSigned() && t2.isUnsigned())
			return t1;

		return t1; // they are both 64-bit signed non-integral types
	}
}