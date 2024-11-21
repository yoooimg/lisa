package it.unive.lisa.util.collections.externalSet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

/**
 * A set of elements that are stored externally from this set. Elements are
 * stored inside an {@link ExternalSetCache} instance that is shared among all
 * the sets created from that instance. This avoid the duplication of the
 * references to the elements, enabling this class' instances to store the
 * indexes of the elements inside the cache instead of the full memory address.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 * 
 * @param <T> the type of elements inside this set
 */
public interface ExternalSet<T> extends Set<T> {

	/**
	 * Yields the cache that this set is connected to.
	 * 
	 * @return the cache
	 */
	ExternalSetCache<T> getCache();

	/**
	 * Adds to this set all elements contained into {@code other}. This method
	 * is faster than {@link #addAll(Collection)} since it directly operates on
	 * the underlying bit set.
	 * 
	 * @param other the other set
	 */
	default void addAll(
			ExternalSet<T> other) {
		if (this == other)
			return;
		if (other == null)
			return;
		if (getCache() != other.getCache())
			return;

		for (T element : other)
			add(element);
	}

	/**
	 * Yields a concrete list containing all the elements corresponding to the
	 * bits in this set.
	 * 
	 * @return the collected elements
	 */
	default Collection<T> collect() {
		List<T> list = new ArrayList<>();
		for (T e : this)
			list.add(e);
		return list;
	}

	/**
	 * Yields a fresh copy of this set, defined over the same cache and
	 * containing the same elements.
	 * 
	 * @return the fresh copy
	 */
	ExternalSet<T> copy();

	/**
	 * Determines if this set contains all elements of another if they share the
	 * same cache. This method is faster than {@link #containsAll(Collection)}
	 * since it directly operates on the underlying bit set.
	 * 
	 * @param other the other set
	 * 
	 * @return {@code true} if and only if {@code other} is included into this
	 *             set
	 */
	default boolean contains(
			ExternalSet<T> other) {
		if (this == other)
			return true;
		if (other == null)
			return false;
		if (getCache() != other.getCache())
			return false;

		for (T element : other)
			if (!contains(element))
				return false;
		return true;
	}

	/**
	 * Determines if this set has at least an element in common with another if
	 * they share the same cache.
	 * 
	 * @param other the other set
	 * 
	 * @return true if and only if this set intersects the other
	 */
	default boolean intersects(
			ExternalSet<T> other) {
		if (this == other)
			return true;
		if (other == null)
			return false;
		if (getCache() != other.getCache())
			return false;

		for (T element : other)
			if (contains(element))
				return true;
		return false;
	}

	/**
	 * Yields the intersection of this set and another. Neither of them gets
	 * modified. If {@code other} is {@code null}, or if the two sets are not
	 * defined over the same cache, this set is returned.
	 * 
	 * @param other the other set
	 * 
	 * @return the intersection of the two sets
	 */
	default ExternalSet<T> intersection(
			ExternalSet<T> other) {
		if (this == other)
			return this;
		if (other == null)
			return this;
		if (getCache() != other.getCache())
			return this;

		ExternalSet<T> result = copy();
		for (T element : other)
			if (!contains(element))
				result.remove(element);
		return result;
	}

	/**
	 * Yields a new set obtained from this by removing the given elements. If
	 * {@code other} is {@code null}, or if the two sets are not defined over
	 * the same cache, this set is returned.
	 * 
	 * @param other the elements to remove
	 * 
	 * @return a set obtained from this by removing the elements in
	 *             {@code other}
	 */
	default ExternalSet<T> difference(
			ExternalSet<T> other) {
		if (this == other)
			return this;
		if (other == null)
			return this;
		if (getCache() != other.getCache())
			return this;

		ExternalSet<T> result = copy();
		for (T element : other)
			if (contains(element))
				result.remove(element);
		return result;
	}

	/**
	 * Yields the union of this set and another. Neither of them gets modified.
	 * If {@code other} is {@code null}, or if the two sets are not defined over
	 * the same cache, this set is returned.
	 * 
	 * @param other the other set
	 * 
	 * @return the union of this set and {@code other}
	 */
	default ExternalSet<T> union(
			ExternalSet<T> other) {
		if (this == other)
			return this;
		if (other == null)
			return this;
		if (getCache() != other.getCache())
			return this;

		ExternalSet<T> result = copy();
		for (T element : other)
			if (!contains(element))
				result.add(element);
		return result;
	}

	/**
	 * Yields {@code true} iff at least one element contained in this set
	 * satisfies the given predicate.
	 * 
	 * @param predicate the predicate to be used for testing the elements
	 * 
	 * @return {@code true} iff that condition holds, {@code false} otherwise
	 */
	default boolean anyMatch(
			Predicate<T> predicate) {
		for (T t : this)
			if (predicate.test(t))
				return true;

		return false;
	}

	/**
	 * Yields {@code true} iff none of the elements contained in this set
	 * satisfy the given predicate.
	 * 
	 * @param predicate the predicate to be used for testing the elements
	 * 
	 * @return {@code true} iff that condition holds, {@code false} otherwise
	 */
	default boolean noneMatch(
			Predicate<T> predicate) {
		for (T t : this)
			if (predicate.test(t))
				return false;

		return true;
	}

	/**
	 * Yields {@code true} iff all the elements contained in this set satisfy
	 * the given predicate.
	 * 
	 * @param predicate the predicate to be used for testing the elements
	 * 
	 * @return {@code true} iff that condition holds, {@code false} otherwise
	 */
	default boolean allMatch(
			Predicate<T> predicate) {
		for (T t : this)
			if (!predicate.test(t))
				return false;

		return true;
	}

	/**
	 * Yields a new external set containing only the elements of this set that
	 * satisfy the given predicate.
	 * 
	 * @param predicate the predicate to be used for testing the elements
	 * 
	 * @return a new external set filtered by {@code predicate}
	 */
	default ExternalSet<T> filter(
			Predicate<T> predicate) {
		ExternalSet<T> result = copy();
		for (T t : this)
			if (!predicate.test(t))
				result.remove(t);

		return result;
	}

	/**
	 * Transforms this set into another set where each element is obtained by
	 * transforming elements of this set.
	 * 
	 * @param transformer the function that transforms single elements of this
	 *                        set
	 * 
	 * @return the transformed set
	 */
	default ExternalSet<T> transform(
			UnaryOperator<T> transformer) {
		ExternalSet<T> result = getCache().mkEmptySet();
		for (T t : this)
			result.add(transformer.apply(t));
		return result;
	}

	/**
	 * Transforms this set into another set where each element is obtained by
	 * transforming elements of this set. Note that each element of this set can
	 * be transformed into multiple elements.
	 * 
	 * @param transformer the function that transforms single elements of this
	 *                        set
	 * 
	 * @return the transformed set
	 */
	default ExternalSet<T> multiTransform(
			Function<T, Collection<T>> transformer) {
		ExternalSet<T> result = getCache().mkEmptySet();
		for (T t : this)
			result.addAll(transformer.apply(t));
		return result;
	}

	/**
	 * Reduces this set to a single element. The result starts at {@code base},
	 * and it is transformed by invoking {@code reducer} on the current result
	 * and each element inside this set.
	 * 
	 * @param base    the initial value for building the result
	 * @param reducer the function that combines two elements into a new result
	 * 
	 * @return the reduced element
	 */
	default T reduce(
			T base,
			BinaryOperator<T> reducer) {
		T result = base;
		for (T t : this)
			result = reducer.apply(result, t);
		return result;
	}

	/**
	 * Yields the first element inside this set.
	 * 
	 * @return the first element
	 * 
	 * @throws NoSuchElementException if this set is empty
	 */
	default T first() {
		if (isEmpty())
			throw new NoSuchElementException();
		return iterator().next();
	}
}
