/* Copyright (c) 2012 Neil Walkinshaw and Kirill Bogdanov
 * 
 * This file is part of StateChum
 * 
 * StateChum is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * StateChum is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with StateChum.  If not, see <http://www.gnu.org/licenses/>.
 */
package statechum.collections;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

import statechum.DeterministicDirectedSparseGraph.VertID;

/**
 * A map backed by an array. Expects key to be convertible to an integer and be non-negative.
 * If a map is a singleton, it is made an instance of a special class to save space. If a singleton
 * is expanded with new elements added and then those elements are removed, it does not revert to
 * a singleton for performance reasons. Such a behaviour is not necessary for the pattern of behaviour
 * utilised by the learner. In principle, it can be implemented so that when the number of elements drops to 
 * the array could be thrown away and reverted to a single pair.
 * <br>
 * Ordinarily, this would have been derived from {@link AbstractMap}, however in the interest of memory use
 * this is not done as it would bring in all the attributes of {@link AbstractMap} that we aim to avoid.
 * <br>
 * Important: this collection does not track modifications, so it will never throw {@link ConcurrentModificationException}
 * but instead may return completely wrong values. This is done to reduce memory footprint when storing
 * tens of millions of entries, some of which could be instances of this class.
 * 
 * @author kirill
 */
public class ArrayMapWithSearch<K extends ConvertibleToInt,V> extends ArrayMapWithSearchPos<K, V> {

	public ArrayMapWithSearch()
	{}
	
	public ArrayMapWithSearch(int currentSize)
	{
		int currentOffset = currentSize*CELLS_PER_ELEM;
		Object[] data = new Object[CELLS_PER_ELEM+currentOffset];
		array_or_key = data;
		zero = 0;// zero is set in the middle.
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public V get(Object k) {
		if (k == null)
			return null;
		if (array_or_key == null)
			return null;
		int kIndex = ((ConvertibleToInt)k).toInt();
		if (array_or_key instanceof ConvertibleToInt)
		{
			if ( ((ConvertibleToInt)array_or_key).toInt() == kIndex)
				return value;
			
			return null;
		}
		Object[] array = (Object[])array_or_key;
		int offset = (kIndex-zero)*CELLS_PER_ELEM;
		if (kIndex < zero || offset >= array.length)
			return null;
		assert offset+1 < array.length: "array length is "+array.length+", kindex="+kIndex+", zero="+zero+", offset="+offset;
		return (V)array[1+offset];
	}

	private int zero=0;
	
	@SuppressWarnings("unchecked")
	@Override
	public V put(K k, V v) {
		V outcome = null;
        if (k == null)
            throw new IllegalArgumentException("key cannot be null for ArrayMapWithSearch");
        if (v == null)
            throw new IllegalArgumentException("value cannot be null for ArrayMapWithSearch");
 		int kIndex = ((ConvertibleToInt)k).toInt();

		if (array_or_key == null)
		{
			array_or_key=k;value=v;
			// outcome remains null
		}
		else
		if (array_or_key instanceof ConvertibleToInt)
		{
			int currentIndex = ((ConvertibleToInt)array_or_key).toInt();
			if (currentIndex == kIndex)
			{// replacing the current value
				outcome = value;value=v;
			}
			else
			{// create a collection
				zero=Math.min(kIndex,currentIndex);
				Object[] data = new Object[CELLS_PER_ELEM*(Math.max(kIndex+1,currentIndex+1)-zero)];
				int offsetCurrent = (currentIndex-zero)*CELLS_PER_ELEM, offsetNew = (kIndex-zero)*CELLS_PER_ELEM;
				data[offsetCurrent]=array_or_key;data[1+offsetCurrent]=value;
				data[offsetNew]=k;data[1+offsetNew]=v;
				array_or_key = data;
				
				// outcome remains null
			}
		}
		else
		{// collection already exists
			Object[] array= (Object[])array_or_key;
			int currentLength = array.length;
			int offset = (kIndex-zero)*CELLS_PER_ELEM;
			if (kIndex < zero)
			{// resize downwards
				int evenStep = currentLength/GROWTHRATE_DIV;if (evenStep % GROWTHRATE_DIV > 0) evenStep-=evenStep % GROWTHRATE_DIV;
				int newSize = currentLength + Math.max( -offset,  evenStep);
				array = new Object[newSize];
				int newZero = Math.min( kIndex, zero-(currentLength/2 /CELLS_PER_ELEM));
				System.arraycopy(array_or_key, 0, array, (zero-newZero)*CELLS_PER_ELEM, currentLength);
				zero=newZero;
				offset = (kIndex-zero)*CELLS_PER_ELEM;
				array_or_key = array;
			}
			else
			if ( offset >= currentLength)
			{// resize upwards
				int evenStep = currentLength/GROWTHRATE_DIV;if (evenStep % GROWTHRATE_DIV > 0) evenStep-=evenStep % GROWTHRATE_DIV;
				int newSize = currentLength + Math.max( offset-currentLength+CELLS_PER_ELEM, evenStep);
				array = new Object[newSize];
				System.arraycopy(array_or_key, 0, array, 0, currentLength);
				array_or_key = array;
			}
			
			assert array.length % GROWTHRATE_DIV == 0;
			outcome = (V)array[1+offset];array[offset]=k;array[1+offset]=v;
		}
		
		return outcome;
	}
	
	// Remove or contains: null/invalid/existing/non-existing
	// Add: key is null/invalid/existing/non-existing
	// Add: value is null/existing/non-existing
	// Values: null/one/two/multiple with repeated values
	// Keyset: null/one/two/multiple
	// Initial collection for add/remove: empty/one/two/multiple
	@SuppressWarnings("unchecked")
	@Override
	public V remove(Object k) {
		V outcome = null;
		if (k == null || array_or_key == null)
			return null;
		int kIndex = ((ConvertibleToInt)k).toInt();
		if (array_or_key instanceof ConvertibleToInt)
		{
			if ( ((ConvertibleToInt)array_or_key).toInt() == kIndex)
			{// remove the only mapping
				outcome = value;
				clear();
			}
		}
		else
		{// we've got an array
			Object[] array = (Object[])array_or_key;
			int offset = (kIndex-zero)*CELLS_PER_ELEM;
			if (kIndex >= zero && offset < array.length)
			{
				outcome = (V)array[1+offset];
				array[offset]=null;array[1+offset]=null;
			}
		}
		return outcome;
	}

	@Override
	public Set<K> keySet() {
		return new AbstractSet<K>(){

			@Override
			public Iterator<K> iterator() {
				return new AnIterator<K>(){
					K lastValue = null;
					
					@SuppressWarnings("unchecked")
					@Override
					public K next() {
						K outcome = null;
						if (!hasNext())// in case we're storing an array, this call will move index to the next non-null if there is any. 
							throw new NoSuchElementException();
						
						if (array_or_key instanceof ConvertibleToInt)
						{
							nextIndex = -1;// this is the only element, force next to negative
							outcome = (K)array_or_key;							
						}
						else
						{
							outcome = (K) ((Object[])array_or_key)[nextIndex];
							nextIndex+=CELLS_PER_ELEM;// move to the next element, we'll be looking for non-nulls in the next call to hasNext()							
						}
						lastValue = outcome;
						return outcome;
					}
					
					@Override
					public void remove()
					{
						if (lastValue == null)
							throw new IllegalStateException("next was not yet called or was already called");
						ArrayMapWithSearch.this.remove(lastValue);
						lastValue = null;
					}
				};
			}

	        @Override
			public boolean contains(Object o) {
	            return containsKey(o);
	        }
	        
	        @Override
	        public boolean remove(Object o) {
	            return ArrayMapWithSearch.this.remove(o) != null;
	        }
	        
	        @Override
			public void clear() {
	        	ArrayMapWithSearch.this.clear();
	        }

			/* (non-Javadoc)
			 * @see java.util.AbstractCollection#add(java.lang.Object)
			 */
			@Override
			public boolean add(@SuppressWarnings("unused") K e) {
				throw new UnsupportedOperationException("modification of key set is not allowed for ArrayMapWithSearch");
			}

			/* (non-Javadoc)
			 * @see java.util.AbstractCollection#addAll(java.util.Collection)
			 */
			@Override
			public boolean addAll(@SuppressWarnings("unused") Collection<? extends K> c) {
				throw new UnsupportedOperationException("modification of key set is not allowed for ArrayMapWithSearch");
			}

			@Override
			public int size() {
				return ArrayMapWithSearch.this.size();
			}
		};
	}

	abstract class AnIterator<IT> implements Iterator<IT>
	{
		int nextIndex = 0;// the first value in an array
		@Override
		public boolean hasNext() {
			if (array_or_key == null)
				return false;
			if (!(array_or_key instanceof ConvertibleToInt))
				updateIndexToNextElement();// we've got an array, position the index to the next non-null
			
			return nextIndex >= 0;
		}

		private void updateIndexToNextElement()
		{
			if (nextIndex >= 0 && array_or_key != null && !(array_or_key instanceof ConvertibleToInt))
			{
				Object[] array=(Object[])array_or_key;
				while(nextIndex < array.length && array[nextIndex] == null)
					nextIndex+=CELLS_PER_ELEM;
				if (nextIndex >= array.length)
					nextIndex = -1;// failed to find another element
			}
		}

		@Override
		public void remove() {
            throw new UnsupportedOperationException("modification of iterator is not allowed for ArrayMapWithSearch");
		}
	}
	
	abstract class Entry<A,B> implements java.util.Map.Entry<A,B>
	{
		@Override
		public int hashCode()
		{
			return getKey().hashCode() ^ getValue().hashCode();
		}
		
		@Override
		public boolean equals(Object obj)
		{
			if (this == obj)
				return true;
			if (!(obj instanceof java.util.Map.Entry))
				return false;
			@SuppressWarnings("unchecked")
			java.util.Map.Entry<A,B> o = (java.util.Map.Entry<A,B>)obj;
			return o.getKey().equals(o.getKey()) && o.getValue().equals(o.getValue());
		}
		
		@Override
		public String toString()
		{
			return getKey().toString()+"="+getValue().toString();
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public K findElementById(VertID id) {
		if (id == null)
			return null;
		if (array_or_key == null)
			return null;
		int kIndex = id.toInt();
		if (array_or_key instanceof ConvertibleToInt)
		{
			if ( ((ConvertibleToInt)array_or_key).toInt() == kIndex)
				return (K)array_or_key;
			
			return null;
		}
		Object[] array = (Object[])array_or_key;
		int offset = (kIndex-zero)*CELLS_PER_ELEM;
		if (kIndex < zero || offset >= array.length)
			return null;
		return (K)array[offset];
	}

}
