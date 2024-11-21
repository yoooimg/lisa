package it.unive.lisa.analysis.lattices;

import it.unive.lisa.analysis.BaseLattice;
import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.util.representation.SetRepresentation;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * A generic set lattice containing a set of elements. Lattice operations
 * correspond to standard set operations:
 * <ul>
 * <li>the lub is the set union</li>
 * <li>the &le; is the set inclusion</li>
 * <li>...</li>
 * </ul>
 * Widening on instances of this lattice depends on the cardinality of the
 * domain of the underlying elements. The provided implementation behave as the
 * domain is <b>finite</b>, thus invoking the lub. Set lattices defined on
 * infinite domains must implement a coherent widening logic.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 * 
 * @param <S> the concrete instance of {@link SetLattice}
 * @param <E> the type of elements of the domain of this lattice
 */
public abstract class SetLattice<S extends SetLattice<S, E>, E> implements BaseLattice<S>, Iterable<E> {

	/**
	 * The set of elements contained in the lattice.
	 */
	public final Set<E> elements;

	/**
	 * Whether or not this is the top or bottom element of the lattice, valid
	 * only if the set of elements is empty.
	 */
	public final boolean isTop;

	/**
	 * Builds the lattice.
	 * 
	 * @param elements the elements that are contained in the lattice
	 * @param isTop    whether or not this is the top or bottom element of the
	 *                     lattice, valid only if the set of elements is empty
	 */
	public SetLattice(
			Set<E> elements,
			boolean isTop) {
		this.elements = elements;
		this.isTop = isTop;
	}

	/**
	 * Utility for creating a concrete instance of {@link SetLattice} given a
	 * set. This decouples the instance of set used during computation of the
	 * elements to put in the lattice from the actual type of set underlying the
	 * lattice.
	 * 
	 * @param set the set containing the elements that must be included in the
	 *                lattice instance
	 * 
	 * @return a new concrete instance of {@link SetLattice} containing the
	 *             elements of the given set
	 */
	public abstract S mk(
			Set<E> set);

	@Override
	public S lubAux(
			S other)
			throws SemanticException {
		Set<E> lub = new HashSet<>(elements);
		lub.addAll(other.elements);
		return mk(lub);
	}

	@Override
	public S glbAux(
			S other)
			throws SemanticException {
		Set<E> glb = new HashSet<>(elements);
		glb.retainAll(other.elements);
		return mk(glb);
	}

	@Override
	public boolean lessOrEqualAux(
			S other)
			throws SemanticException {
		return other.elements.containsAll(elements);
	}

	@Override
	public boolean isTop() {
		return isTop && elements.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return !isTop && elements.isEmpty();
	}

	/**
	 * Checks whether an element is contained in this set.
	 * 
	 * @param elem the element
	 * 
	 * @return {@code true} if the element is contained in this set,
	 *             {@code false} otherwise.
	 */
	public boolean contains(
			E elem) {
		return elements.contains(elem);
	}

	/**
	 * Yields the set of elements contained in this lattice element.
	 * 
	 * @return the set of elements contained in this lattice element.
	 */
	public Set<E> elements() {
		return elements;
	}

	@Override
	public Iterator<E> iterator() {
		return this.elements.iterator();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((elements == null) ? 0 : elements.hashCode());
		result = prime * result + (isTop ? 1231 : 1237);
		return result;
	}

	@Override
	public boolean equals(
			Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		SetLattice<?, ?> other = (SetLattice<?, ?>) obj;
		if (elements == null) {
			if (other.elements != null)
				return false;
		} else if (!elements.equals(other.elements))
			return false;
		if (isTop != other.isTop)
			return false;
		return true;
	}

	@Override
	public final String toString() {
		if (isTop())
			return Lattice.TOP_STRING;

		if (isBottom())
			return Lattice.BOTTOM_STRING;

		return elements.toString();
	}

	/**
	 * Returns the number of elements in this lattice (its cardinality). If this
	 * lattice contains more than {@code Integer.MAX_VALUE} elements, returns
	 * {@code Integer.MAX_VALUE}.
	 *
	 * @return the number of elements in this lattice (its cardinality)
	 */
	public int size() {
		return elements.size();
	}

	/**
	 * Returns {@code true} if this set contains no elements.
	 *
	 * @return {@code true} if this set contains no elements
	 */
	public boolean isEmpty() {
		return elements.isEmpty();
	}

	@Override
	public StructuredRepresentation representation() {
		return new SetRepresentation(elements, StringRepresentation::new);
	}
}
