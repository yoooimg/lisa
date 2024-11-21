package it.unive.lisa.util.collections.externalSet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A cache for creating {@link ExternalSet}s of the elements contained in this
 * cache.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 * 
 * @param <T> the type of elements that this cache stores
 */
public class ExternalSetCache<T> {

	/**
	 * The collection of elements in this cache
	 */
	private final List<T> elements = new ArrayList<>(16);

	/**
	 * A map from the elements to their index
	 */
	private final Map<T, Integer> indexes = new HashMap<>(16);

	/**
	 * The next index available for new elements
	 */
	private int nextIndex = 0;

	/**
	 * The index assigned to the {@code null} key, if any.
	 */
	private int indexOfNull = -1;

	/**
	 * Builds an empty {@link ExternalSet} that uses this cache.
	 * 
	 * @return the empty set
	 */
	public ExternalSet<T> mkEmptySet() {
		return new BitExternalSet<>(this);
	}

	/**
	 * Builds an {@link ExternalSet} that uses this cache and contains the
	 * elements of the given iterable.
	 *
	 * @param iterable the iterable
	 * 
	 * @return the set
	 */
	public ExternalSet<T> mkSet(
			Iterable<T> iterable) {
		return new BitExternalSet<>(this, iterable);
	}

	/**
	 * Builds an {@link ExternalSet} that uses this cache and contains only the
	 * given element.
	 * 
	 * @param element the element
	 * 
	 * @return the set
	 */
	public ExternalSet<T> mkSingletonSet(
			T element) {
		return new BitExternalSet<>(this, element);
	}

	/**
	 * Builds an {@link ExternalSet} that uses this cache and contains all of
	 * its elements. The returned set will stay up to date with this cache.
	 * 
	 * @return the set
	 */
	public ExternalSet<T> mkUniversalSet() {
		return new UniversalExternalSet<>(this);
	}

	/**
	 * Yields the index where the given element is stored in this cache.
	 * 
	 * @param e the element
	 * 
	 * @return the index of {@code e}, or {@code -1}
	 */
	protected final synchronized int indexOf(
			T e) {
		if (e == null)
			return indexOfNull;

		Integer result;
		return (result = indexes.get(e)) == null ? -1 : result;
	}

	/**
	 * Yields the index where the given element is stored in this cache. If the
	 * element is not currently in this cache, it is added.
	 * 
	 * @param e the element
	 * 
	 * @return the index of {@code e}
	 */
	protected final synchronized int indexOfOrAdd(
			T e) {
		if (e == null) {
			if (indexOfNull == -1) {
				elements.add(null);
				indexOfNull = nextIndex++;
			}
			return indexOfNull;
		}

		Integer result = indexes.get(e);
		if (result == null)
			return indexes.computeIfAbsent(e, el -> {
				elements.add(e);
				return nextIndex++;
			});

		return result;
	}

	/**
	 * Yields the {@code pos}-th element of this cache.
	 *
	 * @param pos the position
	 * 
	 * @return the element
	 */
	protected final synchronized T get(
			int pos) {
		return elements.get(pos);
	}

	/**
	 * Cleans the cache, removing all elements.
	 */
	public final synchronized void clear() {
		elements.clear();
		indexes.clear();
		indexOfNull = -1;
		nextIndex = 0;
	}

	/**
	 * Yields the total number of elements stored in this cache.
	 * 
	 * @return the number of elements
	 */
	public final synchronized int size() {
		return elements.size();
	}

	@Override
	public final synchronized String toString() {
		return elements.toString();
	}

	/**
	 * Yields an unmodifiable view of all the elements currently in the cache.
	 * For a view that always stays up-to-date, use {@link #mkUniversalSet()}.
	 * 
	 * @return a view of the elements inside this cache
	 */
	synchronized Collection<T> getAllElements() {
		return Collections.unmodifiableCollection(elements);
	}
}
