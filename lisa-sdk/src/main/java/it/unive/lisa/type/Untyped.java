package it.unive.lisa.type;

import java.util.Set;

/**
 * The untyped type, corresponding to an unknown/untyped type. This type is used
 * as default when no type information is provided for LiSA constructs (e.g.,
 * expression, variable, CFG return type). It implements the singleton design
 * pattern, that is the instances of this type are unique. The unique instance
 * of this type can be retrieved by {@link Untyped#INSTANCE}.
 * 
 * @author <a href="mailto:vincenzo.arceri@unive.it">Vincenzo Arceri</a>
 */
public class Untyped implements Type {

	/**
	 * Unique instance of Untyped type.
	 */
	public static final Untyped INSTANCE = new Untyped();

	/**
	 * Builds the type. This constructor is visible to allow subclassing:
	 * instances of this class should be unique, and the singleton can be
	 * retrieved through field {@link #INSTANCE}.
	 */
	protected Untyped() {
	}

	@Override
	public String toString() {
		return "untyped";
	}

	@Override
	public boolean equals(
			Object other) {
		return other instanceof Untyped;
	}

	@Override
	public int hashCode() {
		return Untyped.class.hashCode();
	}

	@Override
	public boolean canBeAssignedTo(
			Type other) {
		return other == this;
	}

	@Override
	public Type commonSupertype(
			Type other) {
		return this;
	}

	@Override
	public Set<Type> allInstances(
			TypeSystem types) {
		return types.getTypes();
	}
}
