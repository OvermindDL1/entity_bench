use std::cmp::Ordering;
use std::iter::Zip;
use std::slice::{Iter, IterMut};

// TODO:  How on earth does Rust not have GAT's yet?!?  Gaaah, hitting these issues in SO many places!
// /// Trait to implement for user specified storage for the SparseSet.
// pub trait StorageContainer {
// 	/// The element type.
// 	type Element;
// 	/// The shared iterator.
// 	type Iterator;
// 	/// The unique iterator.
// 	type IteratorMut;
// 	/// Reserve space for faster allocation if appropriate.
// 	fn reserve(&mut self, cap: usize);
// 	/// Clear all elements from this container.
// 	fn clear(&mut self);
// 	/// Reduce the memory as much as possible to fit the contained
// 	/// elements without reordering their index
// 	fn shrink_to_fit(&mut self);
// 	/// Push a value to the conceptual 'end' of this container.
// 	///
// 	/// The `idx` is not useful if the container is packed memory, just
// 	/// push it on to the end, however the idx can be useful for other
// 	/// forms of storage, such as partitioning trees as an example.
// 	fn push(&mut self, idx: usize, value: Self::Element);
// 	/// Removes an element replacing it with the last-most element.
// 	///
// 	/// This is essentially a shortcut of a swap and a pop, since pop
// 	/// is not needed.
// 	fn swap_remove(&mut self, idx: usize);
// 	/// Shared Iterator
// 	fn iter(&self) -> Self::Iterator;
// 	/// Unique Iterator
// 	fn iter_mut(&self) -> Self::IteratorMut;
// }
//
// struct StorageContainerCountedIterator(usize);
// impl Iterator for StorageContainerCountedIterator {
// 	type Item = ();
//
// 	fn next(&mut self) -> Option<Self::Item> {
// 		if self.0 > 0 {
// 			self.0 -= 1;
// 			Some(())
// 		} else {
// 			None
// 		}
// 	}
// }
//
// impl<'a> StorageContainer<'a> for usize {
// 	type Element = ();
// 	type Iterator = StorageContainerCountedIterator;
// 	type IteratorMut = StorageContainerCountedIterator;
// 	fn reserve(&mut self, _cap: usize) {}
// 	fn clear(&mut self) {}
// 	fn shrink_to_fit(&mut self) {}
// 	fn push(&mut self, _idx: usize, _value: Self::Element) {}
// 	fn swap_remove(&mut self, idx: usize) {}
// 	fn iter(&self) -> Self::Iterator {
// 		StorageContainerCountedIterator(self)
// 	}
// 	fn iter_mut(&mut self) -> Self::IteratorMut {
// 		StorageContainerCountedIterator(self)
// 	}
// }
//
// impl<'a, T> StorageContainer<'a> for Vec<T> {
// 	type Element = T;
// 	type Iterator = std::slice::Iter<'a, Self::Element>;
// 	type IteratorMut = std::slice::IterMut<'a, Self::Element>;
//
// 	fn reserve(&mut self, cap: usize) {
// 		self.reserve(cap);
// 	}
//
// 	fn clear(&mut self) {
// 		self.clear();
// 	}
//
// 	fn shrink_to_fit(&mut self) {
// 		self.shrink_to_fit();
// 	}
//
// 	fn push(&mut self, _idx: usize, value: Self::Element) {
// 		self.push(value);
// 	}
//
// 	fn swap_remove(&mut self, idx: usize) {
// 		self.swap_remove(idx);
// 	}
//
// 	fn iter(&self) -> Self::Iterator {
// 		self.iter()
// 	}
//
// 	fn iter_mut(&mut self) -> Self::IteratorMut {
// 		self.iter_mut()
// 	}
// }

/// Specialized sparse set implementation.
///
/// Sparse set or packed array or whatever is the name users give it.<br/>
/// Two arrays: an _external_ one and an _internal_ one; a _sparse_ one and a
/// _packed_ one; one used for direct access through contiguous memory, the other
/// one used to get the data through an extra level of indirection.<br/>
/// This is largely used by the registry to offer users the fastest access ever
/// to the components. Views and groups in general are almost entirely designed
/// around sparse sets.
///
/// This type of data structure is widely documented in the literature and on the
/// web. This is nothing more than a customized implementation suitable for the
/// purpose of the framework.
///
/// There are no guarantees that entities are returned in the insertion order
/// when iterate a sparse set. Do not make assumption on the order in any case.
///
/// Internal data structures arrange elements to maximize performance. Because of
/// that, there are no guarantees that elements have the expected order when
/// iterate directly the internal packed array (see `data` and `size` member
/// functions for that). Use `begin` and `end` instead.
#[derive(Clone, Default)]
pub struct SparseSet<EntityType: Entity, StorageElementType> {
    pub reverse: Vec<Vec<usize>>,
    pub direct: Vec<EntityType>,
    pub storage: Vec<StorageElementType>, // TODO: Replace this with StorageContainerType once GAT's exist
}

impl<EntityType: Entity + Ord, StorageElementType> SparseSet<EntityType, StorageElementType> {
    const PAGE_SIZE: usize = 0x8000; // 32768 Must only be a single bit assigned: 0b1000_0000_0000_0000
    const PER_PAGE: usize = Self::PAGE_SIZE / std::mem::size_of::<EntityType>();
    pub const INVALID: usize = std::usize::MAX;

    // Private functions

    fn page(entity: EntityType) -> usize {
        entity.idx() / Self::PER_PAGE
    }

    fn offset(entity: EntityType) -> usize {
        entity.idx() & (Self::PER_PAGE - 1)
    }

    fn assure(&mut self, pos: usize) -> &mut Vec<usize> {
        if pos >= self.reverse.len() {
            self.reverse.resize(pos + 1, vec![]);
        }

        let rev = &mut self.reverse[pos];
        if rev.is_empty() {
            // Then allocate it
            rev.resize(Self::PER_PAGE, Self::INVALID);
        }

        rev
    }

    // Public API

    /// Default constructor.
    ///
    /// ```
    /// let set = &mut enrs::entity::sparse_set::SparseSet::<u32, Vec<i32>>::new();
    /// ```
    pub fn new() -> SparseSet<EntityType, StorageElementType> {
        SparseSet::<EntityType, StorageElementType> {
            reverse: vec![],
            direct: vec![],
            storage: vec![],
        }
    }

    pub fn with_capacity(cap: usize) -> SparseSet<EntityType, StorageElementType> {
        SparseSet::<EntityType, StorageElementType> {
            reverse: Vec::with_capacity((cap / Self::PAGE_SIZE) + 1),
            direct: Vec::with_capacity(cap),
            storage: Vec::with_capacity(cap),
        }
    }

    /// Increases the capacity of a sparse set.
    ///
    /// If the new capacity is greater than the current capacity, new storage is
    /// allocated, otherwise the method does nothing.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, Vec<i32>>::new();
    /// assert_eq!(set.capacity(), 0);
    /// set.reserve(42);
    /// assert_eq!(set.capacity(), 42);
    /// set.reserve(16);
    /// assert_eq!(set.capacity(), 42);
    /// ```
    pub fn reserve(&mut self, cap: usize) {
        self.direct.reserve(cap);
        self.storage.reserve(cap);
    }

    /// Returns the number of elements that a sparse set has currently
    /// allocated space for.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, Vec<i32>>::new();
    /// assert_eq!(set.capacity(), 0);
    /// set.reserve(42);
    /// assert_eq!(set.capacity(), 42);
    /// set.reserve(16);
    /// assert_eq!(set.capacity(), 42);
    /// ```
    pub fn capacity(&self) -> usize {
        self.direct.capacity()
    }

    /// Requests the removal of unused capacity.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, Vec<i32>>::new();
    /// assert_eq!(set.capacity(), 0);
    /// set.reserve(42);
    /// assert_eq!(set.capacity(), 42);
    /// set.reserve(16);
    /// assert_eq!(set.capacity(), 42);
    /// set.shrink_to_fit();
    /// assert_eq!(set.capacity(), 0);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        if self.direct.is_empty() {
            self.storage.clear();
            self.reverse.clear();
        }

        self.storage.shrink_to_fit();
        self.direct.shrink_to_fit();
        self.reverse.shrink_to_fit();
    }

    /// Returns the extent of a sparse set.
    ///
    /// The extent of a sparse set is also the size of the internal sparse array.
    /// There is no guarantee that the internal packed array has the same size.
    /// Usually the size of the internal sparse array is equal or greater than
    /// the one of the internal packed array.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// assert_eq!(set.extent(), 0);
    /// set.insert(1, 1);
    /// assert_eq!(set.extent(), 8192);
    /// # set.insert(9000, 9000);
    /// # assert_eq!(set.extent(), 16384);
    /// ```
    pub fn extent(&self) -> usize {
        self.reverse.len() * Self::PER_PAGE
    }

    /// Returns the number of elements in a sparse set.
    ///
    /// The number of elements is also the size of the internal packed array.
    /// There is no guarantee that the internal sparse array has the same size.
    /// Usually the size of the internal sparse array is equal or greater than
    /// the one of the internal packed array.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(1, 1);
    /// assert_eq!(set.len(), 1);
    /// # set.insert(9000, 9000);
    /// # assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.direct.len()
    }

    /// Checks whether a sparse set is empty.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// assert_eq!(set.is_empty(), true);
    /// set.insert(1, 1);
    /// assert_eq!(set.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.direct.is_empty()
    }

    // TODO:  I really don't like this `data` function, research on use-cases...
    // /// Direct access to the internal packed array.
    // ///
    // /// There are no guarantees on the order, even though `respect` has been
    // /// previously invoked. Internal data structures arrange elements to maximize
    // /// performance. Accessing them directly gives a performance boost but less
    // /// guarantees. Use `begin` and `end` if you want to iterate the sparse set
    // /// in the expected order.
    // ///
    // /// ```
    // /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, ()>::new(());
    // /// assert_eq!(set.data(), &vec![]);
    // /// set.insert(2);
    // /// assert_eq!(set.data(), &vec![2u32]);
    // /// set.insert(1);
    // /// assert_eq!(set.data(), &vec![2u32, 1u32]);
    // /// ```
    // pub fn data(&self) -> &Vec<EntityType> {
    // 	&self.direct
    // }

    /// Checks if a sparse set contains an entity.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// assert_eq!(set.contains(1), false);
    /// set.insert(1, 1);
    /// assert_eq!(set.contains(1), true);
    /// ```
    pub fn contains(&self, entity: EntityType) -> bool {
        let page = Self::page(entity);
        if page >= self.reverse.len() {
            return false;
        }
        let rev = &self.reverse[page];
        if rev.is_empty() {
            return false;
        }
        rev[Self::offset(entity)] != Self::INVALID
    }

    /// Returns the position of an entity in a sparse set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// set.insert(1, 1);
    /// assert_eq!(set.index(1), Some(0));
    /// set.insert(8, 8);
    /// set.insert(4, 4);
    /// assert_eq!(set.index(8), Some(1));
    /// assert_eq!(set.index(4), Some(2));
    /// assert_eq!(set.index(42), None);
    /// ```
    pub fn index(&self, entity: EntityType) -> Option<usize> {
        // #[cfg(not(enrs_disable_asserts))]
        // assert!(self.contains(entity));
        // TODO: unsafe this?  Maybe?
        match self.reverse[Self::page(entity)][Self::offset(entity)] {
            Self::INVALID => None,
            idx => Some(idx),
        }
    }

    /// Assigns an entity to a sparse set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// assert_eq!(set.contains(1), false);
    /// set.insert(1, 1);
    /// assert_eq!(set.contains(1), true);
    /// ```
    pub fn insert(&mut self, entity: EntityType, value: StorageElementType) {
        //#[cfg(not(enrs_disable_asserts))]
        //assert!(!self.contains(entity));
        let idx = self.direct.len();
        self.assure(Self::page(entity))[Self::offset(entity)] = idx;
        self.direct.push(entity);
        self.storage.push(value);
    }

    // TODO: This gains nothing over a standard rust itorator over `insert`, research use-cases for possibly remaking it in some way.
    // /// Assigns one or more entities to a sparse set.
    // ///
    // /// An assertion will abort the execution at runtime in debug mode if the
    // /// sparse set already contains the given entity.
    // ///
    // /// ```
    // /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, ()>::new(());
    // /// assert_eq!(set.contains(1), false);
    // /// assert_eq!(set.contains(2), false);
    // /// assert_eq!(set.contains(3), false);
    // /// set.extend(vec![1, 2, 3]);
    // /// assert_eq!(set.contains(1), true);
    // /// assert_eq!(set.contains(3), true);
    // /// assert_eq!(set.contains(2), true);
    // /// ```
    // pub fn extend<I: IntoIterator<Item = EntityType>>(&mut self, iter: I) {
    // 	let mut next = self.direct.len();
    // 	iter.into_iter().for_each(|entity| {
    // 		#[cfg(not(enrs_disable_asserts))]
    // 		assert!(!self.contains(entity));
    // 		self.assure(Self::page(entity))[Self::offset(entity)] = next;
    // 		next += 1;
    // 		self.direct.push(entity);
    // 	})
    // 	// self.direct.extend(iter);
    // }

    /// Removes an entity from a sparse set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, i32>::new();
    /// assert_eq!(set.contains(1), false);
    /// set.insert(1, 1);
    /// assert_eq!(set.contains(1), true);
    /// # set.insert(2, 2);
    /// # assert_eq!(set.contains(2), true);
    /// set.remove(1);
    /// assert_eq!(set.contains(1), false);
    /// # set.remove(2);
    /// # assert_eq!(set.contains(2), false);
    /// ```
    pub fn remove(&mut self, entity: EntityType) {
        #[cfg(not(enrs_disable_asserts))]
        assert!(self.contains(entity));
        let page = Self::page(entity);
        let offset = Self::offset(entity);
        if self.direct.len() > 1 {
            let pos = self.reverse[page][offset];
            self.storage.swap_remove(pos);
            let back = self.direct[self.direct.len() - 1];
            self.direct[pos] = back;
            self.direct.pop();
            self.reverse[Self::page(back)][Self::offset(back)] = pos;
            self.reverse[page][offset] = Self::INVALID;
        } else {
            self.storage.clear();
            self.direct.clear();
            self.reverse.clear();
        }
    }

    /// Returns a reference to the value associated with an entity.
    ///
    /// Attempting to use an entity that doesn't belong to the storage results in
    /// a panic.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// set.insert(1, 42);
    /// assert_eq!(set.get(1), &42);
    /// ```
    pub fn get(&self, entity: EntityType) -> &StorageElementType {
        let index = self.reverse[Self::page(entity)][Self::offset(entity)];
        &self.storage[index]
    }

    /// Returns a mutable reference to the value associated with an entity.
    ///
    /// Attempting to use an entity that doesn't belong to the storage results in
    /// a panic.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// set.insert(1, 21);
    /// *set.get_mut(1) *= 2;
    /// assert_eq!(set.get(1), &42);
    /// ```
    pub fn get_mut(&mut self, entity: EntityType) -> &mut StorageElementType {
        let index = self.reverse[Self::page(entity)][Self::offset(entity)];
        &mut self.storage[index]
    }

    /// Returns a reference to the value associated with an entity.
    ///
    /// Attempting to use an entity that doesn't belong to the storage results in
    /// a panic.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// assert_eq!(set.try_get(1), None);
    /// set.insert(1, 42);
    /// assert_eq!(set.try_get(1), Some(&42));
    /// ```
    pub fn try_get(&self, entity: EntityType) -> Option<&StorageElementType> {
        let page = Self::page(entity);
        if page >= self.reverse.len() {
            return None;
        }
        let rev = &self.reverse[page];
        if rev.is_empty() {
            return None;
        }
        let index = rev[Self::offset(entity)];
        if index == Self::INVALID {
            return None;
        }
        Some(&self.storage[index])
    }

    /// Returns a mutable reference to the value associated with an entity.
    ///
    /// Attempting to use an entity that doesn't belong to the storage results in
    /// a panic.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// assert_eq!(set.try_get_mut(1), None);
    /// set.insert(1, 21);
    /// *set.try_get_mut(1) .unwrap()*= 2;
    /// assert_eq!(set.get(1), &42);
    /// ```
    pub fn try_get_mut(&mut self, entity: EntityType) -> Option<&mut StorageElementType> {
        let page = Self::page(entity);
        if page >= self.reverse.len() {
            return None;
        }
        let rev = &self.reverse[page];
        if rev.is_empty() {
            return None;
        }
        let index = rev[Self::offset(entity)];
        if index == Self::INVALID {
            return None;
        }
        Some(&mut self.storage[index])
    }

    /// Acquire a shared iterator to the Entities used by this set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [1, 2, 3, 4, 5].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.entities().as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    pub fn entities(&self) -> Iter<EntityType> {
        self.direct.iter()
    }

    /// Acquire a shared iterator to the Values used by entities in this set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [1, 2, 3, 4, 5].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.values().as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    pub fn values(&self) -> Iter<StorageElementType> {
        self.storage.iter()
    }

    /// Acquire a unique iterator to the Values used by entities in this set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [1, 2, 3, 4, 5].iter().for_each(|&i| set.insert(i, i));
    /// set.values_mut().for_each(|v| {*v *= 2;});
    /// assert_eq!(set.values().as_slice(), &[2, 4, 6, 8, 10]);
    /// ```
    pub fn values_mut(&mut self) -> IterMut<StorageElementType> {
        self.storage.iter_mut()
    }

    /// Acquire a shared reference iterator to the packed storage.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [1, 2, 3, 4, 5].iter().for_each(|&i| set.insert(i, i));
    /// set.values_mut().for_each(|v| {*v *= 2;});
    /// let mut it = set.iter();
    /// assert_eq!(it.next(), Some((&1, &2)));
    /// assert_eq!(it.next(), Some((&2, &4)));
    /// assert_eq!(it.next(), Some((&3, &6)));
    /// assert_eq!(it.next(), Some((&4, &8)));
    /// assert_eq!(it.next(), Some((&5, &10)));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn iter(&self) -> Zip<Iter<EntityType>, Iter<StorageElementType>> {
        self.direct.iter().zip(self.storage.iter())
    }

    /// Acquire a unique reference iterator to the packed storage.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [1, 2, 3, 4, 5].iter().for_each(|&i| set.insert(i, i));
    /// set.iter_mut().for_each(|(e, v)| {*v *= 2;}); // e is still not mutable of course
    /// let mut it = set.iter();
    /// assert_eq!(it.next(), Some((&1, &2)));
    /// assert_eq!(it.next(), Some((&2, &4)));
    /// assert_eq!(it.next(), Some((&3, &6)));
    /// assert_eq!(it.next(), Some((&4, &8)));
    /// assert_eq!(it.next(), Some((&5, &10)));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> Zip<Iter<EntityType>, IterMut<StorageElementType>> {
        self.direct.iter().zip(self.storage.iter_mut())
    }

    //	/// Swaps two entities in the internal packed array.
    //	///
    //	/// The entities *must* both already be in this set.
    //	///
    //	/// ```
    //	/// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32>::new();
    //	/// set.extend(vec![1, 2, 3]);
    //	/// assert_eq!(set.index(1), 0);
    //	/// assert_eq!(set.index(2), 1);
    //	/// assert_eq!(set.index(3), 2);
    //	/// set.swap(1, 3);
    //	/// assert_eq!(set.index(1), 2);
    //	/// assert_eq!(set.index(2), 1);
    //	/// assert_eq!(set.index(3), 0);
    //	/// ```
    //	pub fn swap(&mut self, lhs: EntityType, rhs: EntityType) {
    //		// TODO: This could use some massaging... how to swap two elements in potentially different
    //		// TODO: rows of a 2D array without borrowing issues...
    //		let from = self.reverse[Self::page(lhs)][Self::offset(lhs)];
    //		let to = &mut self.reverse[Self::page(rhs)][Self::offset(rhs)];
    //		self.direct.swap(from, *to);
    //		let old_to = *to;
    //		*to = from;
    //		self.reverse[Self::page(lhs)][Self::offset(lhs)] = old_to;
    //	}

    /// If the internal index is sorted and/or shuffled (not added/removed) from directly, use this
    /// to rebuild the internal jump array.  In general users shouldn't need to touch this.
    pub(self) fn rebuild_reverse_index(&mut self) {
        if std::mem::size_of::<StorageElementType>() != 0 {
            self.rebuild_reverse_index_notify(|_, _, _, _| ())
        } else {
            for (idx, entity) in self.direct.iter().enumerate() {
                self.reverse[Self::page(*entity)][Self::offset(*entity)] = idx;
            }
        }
    }

    /// If the internal index is sorted and/or shuffled (not added/removed) from directly, use this
    /// to rebuild the internal jump array.  In general users shouldn't need to touch this.
    ///
    /// This version calls the notification function when ordering has changed on entities to allow
    /// updating of other storage.
    pub(self) fn rebuild_reverse_index_notify<U>(&mut self, mut apply: U)
    where
        U: FnMut(EntityType, usize, EntityType, usize) -> (),
    {
        for (idx, entity) in self.direct.iter().enumerate() {
            let mut curr = idx;
            // let mut next = self.index(*entity);
            let mut next = self.reverse[Self::page(*entity)][Self::offset(*entity)];
            while curr != next {
                self.storage.swap(curr, next);
                let entity_now = self.direct[curr];
                let entity_next = self.direct[next];
                apply(entity_now, curr, entity_next, next);
                self.reverse[Self::page(entity_now)][Self::offset(entity_now)] = curr;
                self.reverse[Self::page(entity_next)][Self::offset(entity_next)] = next;
                curr = next;
                next = self.reverse[Self::page(entity_next)][Self::offset(entity_next)];
            }
        }
    }

    /// Sort the internal array's elements based on their Entity Index in ascending order.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 1].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.index(1), Some(2));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(0));
    /// set.sort();
    /// assert_eq!(set.index(1), Some(0));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(2));
    /// ```
    pub fn sort(&mut self) {
        self.direct.sort_by(|l, r| l.idx().cmp(&r.idx()));
        self.rebuild_reverse_index();
    }

    /// Sort elements according to the given comparison function.
    ///
    /// ```
    /// # use enrs::entity::entity::*;
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 1].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.index(1), Some(2));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(0));
    /// set.sort_by(|l, r| l.idx().cmp(&r.idx())); // Don't normally do this
    /// assert_eq!(set.index(1), Some(0));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(2));
    /// ```
    pub fn sort_by<C: FnMut(&EntityType, &EntityType) -> Ordering>(&mut self, compare: C) {
        self.direct.sort_by(compare);
        self.rebuild_reverse_index();
    }

    /// Sort elements using the given sort function over `Vec<EntityType>`.
    ///
    /// ```
    /// # use enrs::entity::entity::*;
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 1].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.index(1), Some(2));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(0));
    /// set.sort_func(|v| v.sort_by(|l, r|l.idx().cmp(&r.idx()))); // Don't normally do this
    /// assert_eq!(set.index(1), Some(0));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(2));
    /// ```
    pub fn sort_func<S: FnOnce(&mut Vec<EntityType>) -> ()>(&mut self, sort: S) {
        sort(&mut self.direct);
        self.rebuild_reverse_index();
    }

    /// Sort the internal array's elements based on their Entity Index in ascending order.
    ///
    /// This is like `sort` except slightly slower due to extra checks, however it calls a user
    /// callback function to be called when some ordering has changed, this is to allow the user to
    /// update their own data storage to match.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 1].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.index(1), Some(2));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(0));
    ///	let mut entities = vec![3u32, 2u32, 1u32];
    ///	set.sort_with_callback(|e1, i1, e2, i2| { entities.swap(i1, i2); });
    /// assert_eq!(entities, vec![1u32, 2u32, 3u32]);
    /// assert_eq!(set.index(1), Some(0));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(2));
    /// ```
    pub fn sort_with_callback<U: FnMut(EntityType, usize, EntityType, usize) -> ()>(
        &mut self,
        apply: U,
    ) {
        self.direct.sort_by(|l, r| l.idx().cmp(&r.idx()));
        self.rebuild_reverse_index_notify(apply);
    }

    /// Sort elements according to the given comparison function.
    ///
    /// This is like `sort_by` except slightly slower due to extra checks, however it calls a user
    /// callback function to be called when some ordering has changed, this is to allow the user to
    /// update their own data storage to match.
    ///
    /// ```
    /// # use enrs::entity::entity::*;
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 1].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.index(1), Some(2));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(0));
    ///	let mut entities = vec![3u32, 2u32, 1u32];
    ///	set.sort_by_with_callback(|l, r| l.idx().cmp(&r.idx()), |e1, i1, e2, i2| { entities.swap(i1, i2); }); // Don't normally do this
    /// assert_eq!(entities, vec![1u32, 2u32, 3u32]);
    /// assert_eq!(set.index(1), Some(0));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(2));
    /// ```
    pub fn sort_by_with_callback<C, U>(&mut self, compare: C, apply: U)
    where
        C: FnMut(&EntityType, &EntityType) -> Ordering,
        U: FnMut(EntityType, usize, EntityType, usize) -> (),
    {
        self.direct.sort_by(compare);
        self.rebuild_reverse_index_notify(apply);
    }

    /// Sort elements using the given sort function over `Vec<EntityType>`.
    ///
    /// This is like `sort_func` except slightly slower due to extra checks, however it calls a user
    /// callback function to be called when some ordering has changed, this is to allow the user to
    /// update their own data storage to match.
    ///
    /// ```
    /// # use enrs::entity::entity::*;
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 1].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.index(1), Some(2));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(0));
    ///	let mut entities = vec![3u32, 2u32, 1u32];
    ///	set.sort_func_with_callback(|v| v.sort_by(|l, r|l.idx().cmp(&r.idx())), |e1, i1, e2, i2| { entities.swap(i1, i2); }); // Don't normally do this
    /// assert_eq!(entities, vec![1u32, 2u32, 3u32]);
    /// assert_eq!(set.index(1), Some(0));
    /// assert_eq!(set.index(2), Some(1));
    /// assert_eq!(set.index(3), Some(2));
    /// ```
    pub fn sort_func_with_callback<S, U>(&mut self, sort: S, apply: U)
    where
        S: FnOnce(&mut Vec<EntityType>) -> (),
        U: FnMut(EntityType, usize, EntityType, usize) -> (),
    {
        sort(&mut self.direct);
        self.rebuild_reverse_index_notify(apply);
    }

    /// Sort entities according to their order in another sparse set.
    ///
    /// Entities that are part of both the sparse sets are ordered internally
    /// according to the order they have in `other`. All the other entities goes
    /// to the end of the list and there are no guarantees on their order.<br/>
    /// In other terms, this function can be used to impose the same order on two
    /// sets by using one of them as a master and the other one as a slave.
    ///
    /// Attempting to iterate elements using a raw pointer returned by a call to
    /// `data` gives no guarantees on the order, even though `respect` has been
    /// invoked.
    ///
    /// ```
    /// # use enrs::entity::entity::*;
    /// # let set1 = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [1, 2, 3].iter().for_each(|&i| set1.insert(i, i));
    /// # let set2 = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// [3, 2, 4, 1, 5].iter().for_each(|&i| set2.insert(i, i));
    /// set2.sort_as(&set1);
    /// assert_eq!(set2.index(1), Some(2));
    /// assert_eq!(set2.index(2), Some(3));
    /// assert_eq!(set2.index(3), Some(4));
    /// assert!(set2.index(4).unwrap() <= 1);
    /// assert!(set2.index(5).unwrap() <= 1);
    /// ```
    pub fn sort_as<OtherStorageElementType>(
        &mut self,
        other: &SparseSet<EntityType, OtherStorageElementType>,
    ) {
        if !self.direct.is_empty() && !other.direct.is_empty() {
            let mut pos = self.direct.len() - 1;
            for from in other.entities().rev() {
                if pos == 0 {
                    break;
                }
                if self.contains(*from) {
                    let here = self.direct[pos];
                    if *from != here {
                        let to = &mut self.reverse[Self::page(*from)][Self::offset(*from)];
                        self.storage.swap(pos, *to);
                        //self.swap(here, *from);
                        // let to = &mut self.reverse[Self::page(*from)][Self::offset(*from)];
                        self.direct.swap(pos, *to);
                        let old_to = *to;
                        *to = pos;
                        self.reverse[Self::page(here)][Self::offset(here)] = old_to;
                    }
                    pos -= 1;
                }
            }
        }
    }

    /// Clears a sparse set.
    ///
    /// ```
    /// # let set = &mut enrs::entity::sparse_set::SparseSet::<u32, u32>::new();
    /// assert_eq!(set.len(), 0);
    /// set.clear();
    /// assert_eq!(set.len(), 0);
    /// [1, 2, 3].iter().for_each(|&i| set.insert(i, i));
    /// assert_eq!(set.len(), 3);
    /// set.clear();
    /// assert_eq!(set.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.reverse.clear();
        self.direct.clear();
        self.storage.clear();
    }
}

mod private {
    use super::SparseSet;

    pub trait Sealed {}
    impl<EntityType: super::Entity, StorageElementType> Sealed
        for SparseSet<EntityType, StorageElementType>
    {
    }
    // impl<EntityType: super::Entity, StorageElementType> Sealed
    //     for ComponentPool<EntityType, StorageElementType>
    // {
    // }
}

pub trait ErasedSparseSet<EntityType: Entity>: private::Sealed {
    fn reserve(&mut self, cap: usize);
    fn capacity(&self) -> usize;
    fn shrink_to_fit(&mut self);
    fn extent(&self) -> usize;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn contains(&self, entity: EntityType) -> bool;
    fn index(&self, entity: EntityType) -> Option<usize>;
    // fn insert(&mut self, entity: EntityType, value: StorageElementType);
    // fn remove(&mut self, entity: EntityType);
    // fn get(&self, entity: EntityType) -> &StorageElementType;
    // fn get_mut(&mut self, entity: EntityType) -> &mut StorageElementType;
    // fn try_get(&self, entity: EntityType) -> Option<&StorageElementType>;
    // fn try_get(&self, entity: EntityType) -> Option<&StorageElementType>;
    fn entities(&self) -> Iter<EntityType>;
    // fn values(&self) -> Iter<StorageElementType>;
    // fn values_mut(&mut self) -> IterMut<StorageElementType>;
    // fn iter(&self) -> Zip<Iter<EntityType>, Iter<StorageElementType>>;
    // fn iter_mut(&mut self) -> Zip<Iter<EntityType>, IterMut<StorageElementType>>;
    // fn sort(&mut self);
    // fn sort_by<C: FnMut(&EntityType, &EntityType) -> Ordering>(&mut self, compare: C);
    // fn sort_func<S: FnOnce(&mut Vec<EntityType>) -> ()>(&mut self, sort: S);
    // fn sort_with_callback<U: FnMut(EntityType, usize, EntityType, usize) -> ()>(&mut self, apply: U);
    // fn sort_by_with_callback<C, U>(&mut self, compare: C, apply: U)
    //	where
    //		C: FnMut(&EntityType, &EntityType) -> Ordering,
    //		U: FnMut(EntityType, usize, EntityType, usize) -> ();
    // fn sort_func_with_callback<S, U>(&mut self, sort: S, apply: U)
    //	where
    //		S: FnOnce(&mut Vec<EntityType>) -> (),
    //		U: FnMut(EntityType, usize, EntityType, usize) -> ();
    // fn sort_as<OtherStorageElementType>(&mut self, other: &SparseSet<EntityType, OtherStorageElementType>);
    // fn clear(&mut self);
}

// impl<EntityType: Entity, StorageElementType> ErasedSparseSet<EntityType>
//     for ComponentPool<EntityType, StorageElementType>
// {
//     fn reserve(&mut self, cap: usize) {
//         self.reserve(cap)
//     }
//
//     fn capacity(&self) -> usize {
//         self.capacity()
//     }
//
//     fn shrink_to_fit(&mut self) {
//         self.shrink_to_fit()
//     }
//
//     fn extent(&self) -> usize {
//         self.extent()
//     }
//
//     fn len(&self) -> usize {
//         self.len()
//     }
//
//     fn is_empty(&self) -> bool {
//         self.is_empty()
//     }
//
//     fn contains(&self, entity: EntityType) -> bool {
//         self.contains(entity)
//     }
//
//     fn index(&self, entity: EntityType) -> Option<usize> {
//         self.index(entity)
//     }
//
//     fn entities(&self) -> Iter<EntityType> {
//         self.entities()
//     }
// }

impl<EntityType: Entity, StorageElementType> ErasedSparseSet<EntityType>
    for SparseSet<EntityType, StorageElementType>
{
    fn reserve(&mut self, cap: usize) {
        self.reserve(cap)
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit()
    }

    fn extent(&self) -> usize {
        self.extent()
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn contains(&self, entity: EntityType) -> bool {
        self.contains(entity)
    }

    fn index(&self, entity: EntityType) -> Option<usize> {
        self.index(entity)
    }

    fn entities(&self) -> Iter<EntityType> {
        self.entities()
    }
}

/// Move into an iterator, consuming the SparseSet.
impl<EntityType: Entity, StorageElementType> IntoIterator
    for SparseSet<EntityType, StorageElementType>
{
    type Item = EntityType;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.direct.into_iter()
    }
}

/// An iterator over the elements of the SparseSet.
impl<'a, EntityType: Entity, StorageElementType> IntoIterator
    for &'a SparseSet<EntityType, StorageElementType>
{
    type Item = &'a EntityType;
    type IntoIter = Iter<'a, EntityType>;

    fn into_iter(self) -> Self::IntoIter {
        self.direct.iter()
    }
}

/// An iterator over mutable elements of the SparseSet.
impl<'a, EntityType: Entity, StorageElementType> IntoIterator
    for &'a mut SparseSet<EntityType, StorageElementType>
{
    type Item = &'a mut EntityType;
    type IntoIter = IterMut<'a, EntityType>;

    fn into_iter(self) -> Self::IntoIter {
        self.direct.iter_mut()
    }
}

use std::sync::RwLockWriteGuard;

pub struct EntityRegistry<EntityType: Entity> {
    /// `entities` is interesting in that alive ones have their internal index
    /// match their actual index, if it's dead they don't.  If it's dead the
    /// internal index actually points to the actual index of the next 'dead'
    /// one, thus making a handle-based link-list.  If it points to
    /// `0` then there are no more dead entities and a new one needs to be
    /// created.  The generation gets incremented on destruction.
    entities: Vec<EntityType>,
    /// This is the 'head' of the singly-linked list of destroyed entities.
    destroyed: EntityType,
}

impl<EntityType: Entity> Default for EntityRegistry<EntityType> {
    fn default() -> Self {
        EntityRegistry::<EntityType> {
            entities: vec![EntityType::new(0)],
            destroyed: EntityType::new(0),
        }
    }
}

impl<EntityType: Entity> EntityRegistry<EntityType> {
    /// Returns the number of existing entities
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// assert_eq!(registry.size(), 1); // There is always the null/0 entity
    /// registry.create();
    /// assert_eq!(registry.size(), 2);
    /// registry.create();
    /// assert_eq!(registry.size(), 3);
    /// ```
    pub fn size(&self) -> usize {
        self.entities.len()
    }

    /// Returns the number of entities still in use.
    ///
    /// This has to iterate the destroyed entities, it's not fast.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// assert_eq!(registry.alive(), 0);
    /// let entity1 = registry.create();
    /// assert_eq!(registry.alive(), 1);
    /// let entity2 = registry.create();
    /// assert_eq!(registry.alive(), 2);
    /// # //registry.destroy(entity1);
    /// # //assert_eq!(registry.alive(), 1);
    /// # //registry.destroy(entity2);
    /// # //assert_eq!(registry.alive(), 0);
    /// ```
    pub fn alive(&self) -> usize {
        let mut count = self.entities.len() - 1; // -1 for the null/0 entity
        let mut idx = self.destroyed.idx();
        // TODO: Make the array lookup an `unsafe` `get_unchecked` as it's always in range anyway?
        while idx != 0 {
            idx = self.entities[idx].idx();
            count -= 1;
        }
        count
    }

    /// Returns the number of entities that a registry has currently
    /// allocated space for.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// assert!(registry.capacity() >= 1); // There is always the null/0 entity
    /// let entity1 = registry.create();
    /// assert!(registry.capacity() >= 2);
    /// let entity2 = registry.create();
    /// assert!(registry.capacity() >= 3);
    /// # //registry.destroy(entity1);
    /// # //assert!(registry.capacity() >= 3);
    /// # //registry.destroy(entity2);
    /// # //assert!(registry.capacity() >= 3);
    /// ```
    pub fn capacity(&self) -> usize {
        self.entities.capacity()
    }

    /// Checks if an entity identifier refers to a valid entity.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity1 = registry.create();
    /// assert!(registry.valid(entity1));
    /// assert!(!registry.valid(2));
    /// # //registry.destroy(entity1);
    /// # //assert!(!registry.valid(entity1));
    /// ```
    pub fn valid(&self, entity: EntityType) -> bool {
        let idx = entity.idx();
        (idx < self.entities.len()) && self.entities[idx] == entity
    }

    // TODO: What's the point of this `BasicRegistry::entity` function?
    /// Returns the entity identifier without the version.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity1 = registry.create();
    /// assert_eq!(entity1, 0x000_00001);
    /// assert_eq!(enrs::entity::registries::EntityRegistry::<u32>::entity(entity1), 0x000_00001);
    /// # //registry.destroy(entity1);
    /// # //let entity1 = registry.create();
    /// # //assert_eq!(entity1, 0x001_00001);
    /// # //assert_eq!(enrs::entity::registries::EntityRegistry::<u32>::entity(entity1), 0x000_00001);
    /// ```
    pub fn entity(entity: EntityType) -> EntityType {
        EntityType::new(entity.idx())
    }

    /// Returns the version stored along with an entity identifier.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity1 = registry.create();
    /// assert_eq!(entity1, 0x000_00001);
    /// assert_eq!(enrs::entity::registries::EntityRegistry::<u32>::version(entity1), 0);
    /// # //registry.destroy(entity1);
    /// # //let entity1 = registry.create();
    /// # //assert_eq!(entity1, 0x001_00001);
    /// # //assert_eq!(enrs::entity::registries::EntityRegistry::<u32>::version(entity1), 1);
    /// ```
    pub fn version(entity: EntityType) -> EntityType::VersionType {
        entity.version()
    }

    /// Returns the actual version for an entity identifier.
    ///
    /// WARNING:
    ///
    /// Attempting to use an entity that doesn't belong to the registry results
    /// in undefined behavior. An entity belongs to the registry even if it has
    /// been previously destroyed and/or recycled.
    ///
    /// An assertion will abort the execution at runtime in debug mode if the
    /// registry doesn't own the given entity.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity1 = registry.create();
    /// assert_eq!(registry.current(entity1), 0);
    /// # //registry.destroy(entity1);
    /// # //let entity1 = registry.create();
    /// # //assert_eq!(registry.current(entity1), 1);
    /// ```
    pub fn current(&self, entity: EntityType) -> EntityType::VersionType {
        let idx = entity.idx();
        #[cfg(not(enrs_disable_asserts))]
        assert!(idx < self.entities.len());
        self.entities[idx].version()
    }

    /// Creates a new entity and returns it.
    ///
    /// There are two kinds of possible entity identifiers:
    ///
    /// * Newly created ones in case no entities have been previously destroyed.
    /// * Recycled ones with updated versions.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity1 = registry.create();
    /// let entity2 = registry.create();
    /// assert_eq!(entity1, 0x00000001);
    /// assert_eq!(entity2, 0x00000002);
    /// ```
    pub fn create(&mut self) -> EntityType {
        if self.destroyed.is_null() {
            // `destroyed` linked list is empty
            let entity = EntityType::new(self.entities.len());
            self.entities.push(entity);
            entity
        } else {
            let head = self.destroyed.idx();
            // TODO:  This should be safe to make unsafe and use `get_unchecked`
            let head_entity = &mut self.entities[head];
            self.destroyed = EntityType::new(head_entity.idx()); // New head of destroyed list
            *head_entity.set_idx(head)
        }
    }

    /// Creates a new entity and returns it.
    ///
    /// See also: `create`
    ///
    /// If the requested entity isn't in use, the suggested identifier is created
    /// and returned. Otherwise, a new one will be generated for this purpose.
    ///
    /// ```
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity4 = registry.create_hinted(4);
    /// let entity3 = registry.create_hinted(4);
    /// assert_eq!(entity4, 0x00000004);
    /// //assert!(!registry.valid(1));
    /// assert_eq!(entity3, 0x00000003);
    /// ```
    pub fn create_hinted(&mut self, hint: EntityType) -> EntityType {
        #[cfg(not(enrs_disable_asserts))]
        assert!(!hint.is_null());
        let req = hint.idx();
        if req >= self.entities.len() {
            // Overflows, create destroyed entities until filled
            let destroy_count = req - self.entities.len();
            self.entities.reserve(destroy_count + 1);
            for idx in self.entities.len()..req {
                self.entities.push(self.destroyed);
                self.destroyed = EntityType::new(idx);
            }
            self.entities.push(hint);
            hint
        } else {
            let curr = self.entities[req].idx();
            if req == curr {
                // Already an active index, create a new one
                self.create()
            } else {
                // Exists and is destroyed, create it, this means walking the destroyed linked list though...
                let mut idx = self.destroyed.idx();
                if idx == req {
                    // TODO: Should `unsafe` these arrays access to call `get_unchecked` as it will always be in range...
                    let head_entity = &mut self.entities[idx];
                    self.destroyed = EntityType::new(idx);
                    *head_entity.set_idx(idx)
                } else {
                    while idx != req {
                        // TODO: Should `unsafe` these arrays access to call `get_unchecked` as it will always be in range...
                        idx = self.entities[idx].idx();
                    }
                    // TODO: Should `unsafe` these arrays access to call `get_unchecked` as it will always be in range...
                    self.entities[idx].set_idx(curr);
                    let ret = &mut self.entities[req];
                    *ret = hint;
                    *ret
                }
            }
        }
    }

    /// Destroys an entity and lets the registry recycle the identifier.
    ///
    /// When an entity is destroyed, its version is updated and the identifier
    /// can be recycled at any time.
    ///
    /// WARNING:
    ///
    /// In case there are listeners that observe the destruction of components
    /// and assign other components to the entity in their bodies, the result of
    /// invoking this function may not be as expected. In the worst case, it
    /// could lead to undefined behavior. An assertion will abort the execution
    /// at runtime in debug mode if a violation is detected.
    ///
    /// WARNING:
    ///
    /// Attempting to use an invalid entity results in undefined behavior.
    ///
    /// An assertion will abort the execution at runtime in debug mode in case of
    /// invalid entity.
    ///
    /// ```
    /// # use enrs::entity::entity::Entity;
    /// let mut registry = enrs::entity::registries::EntityRegistry::<u32>::default();
    /// let entity1 = registry.create();
    /// let entity2 = registry.create();
    /// assert_eq!(entity1, 0x00000001);
    /// assert_eq!(entity2, 0x00000002);
    /// // registry.assign(entity1, 42u32);
    /// registry.destroy(entity1);
    /// let entity1 = registry.create();
    /// assert_eq!(entity1, 0x00100001);
    /// ```
    pub fn destroy(&mut self, entity: EntityType) {
        #[cfg(not(enrs_disable_asserts))]
        assert!(self.valid(entity));
        let idx = entity.idx();
        (&mut self.entities[idx]).bump_version_with_idx(self.destroyed.idx());
        self.destroyed = EntityType::new(idx);
    }
}

/// Iterator that endlessly creates entities, should always `take` an amount or so.
/// And be sure to consume it as iterators are lazy.
pub struct EntityRegistryCreateIterator<'a, EntityType: Entity>(
    pub(crate) RwLockWriteGuard<'a, EntityRegistry<EntityType>>,
);

impl<'a, EntityType: Entity> Iterator for EntityRegistryCreateIterator<'a, EntityType> {
    type Item = EntityType;

    #[inline(always)]
    fn next(&mut self) -> Option<EntityType> {
        Some(self.0.create())
    }
}

/// Iterator that endlessly creates entities via an iterator of hints, should always `take` an
/// amount or so.  And be sure to consume it as iterators are lazy.
///
/// This returns a tuple of both the hint and the new value to efficiently test if it actually
/// created the same one or if it had to create a new one.  The first value of the tuple is the
/// hint, the second is the new entity value, like `(hint, new)`.
pub struct EntityRegistryCreateHintedIterator<
    'a,
    EntityType: Entity + Copy,
    I: Iterator<Item = EntityType>,
>(
    pub(crate) RwLockWriteGuard<'a, EntityRegistry<EntityType>>,
    pub(crate) I,
);

impl<'a, EntityType: Entity + Copy, I: Iterator<Item = EntityType>> Iterator
    for EntityRegistryCreateHintedIterator<'a, EntityType, I>
{
    type Item = (EntityType, EntityType);

    #[inline(always)]
    fn next(&mut self) -> Option<(EntityType, EntityType)> {
        let hint = self.1.next()?;
        Some((hint, self.0.create_hinted(hint.clone())))
    }
}

/// Entity Type Trait to allow for a variety of entity storages to be used.
///
/// Can make a trivial tuple wrapper with the `delegate_wrapped_entity!` macro:
///
/// ```
/// # use enrs::{delegate_wrapped_entity, entity::entity::Entity};
/// #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// struct Wrapper(u32);
/// delegate_wrapped_entity!(Wrapper, u32);
/// ```
pub trait Entity: PartialEq + Copy + Ord {
    /// The actual container type of this entity date, it should be Copy, and thus cheap to Copy.
    type StorageType;

    /// The type returned to hold the version, smaller than the StorageType in general.
    type VersionType;
    //	type DifferenceType;
    //	const ENTITY_MASK: Self::StorageType;
    //	const VERSION_MASK: Self::StorageType;
    //	const ENTITY_SHIFT: u32;
    ///// Must be what `Self::new(0)` returns.
    //const NULL: Self;
    /// Constructs an Entity Handle using the given ID and a 0 version
    fn new(id: usize) -> Self;
    //	fn to_integral(self) -> Self::StorageType;
    /// Return true if this entity is index 0
    fn is_null(self) -> bool;
    //	fn id(self) -> Self::StorageType;
    /// Returns the index of this entity
    fn idx(self) -> usize;
    /// Sets the index of this entity
    fn set_idx(&mut self, idx: usize) -> &mut Self;
    /// Returns the version of this entity, generally a number but it could potentially be something else, like a UUID
    fn version(self) -> Self::VersionType;
    /// Sets the index as well as increments the version in a single call
    fn bump_version_with_idx(&mut self, idx: usize);
    //	fn new_next_version(self) -> Self;
    //	fn set_version(&mut self, version: Self::StorageType) {
    //		*self = self.new_version(version);
    //	}
    //	fn next_version(&mut self) {
    //		*self = self.new_next_version()
    //	}
}

#[macro_export]
macro_rules! unsigned_integral_entity {
	($INT:ident, $INT_VERSION:ident, $INDEX_MASK:literal, $VERSION_MASK:literal, $SHIFT_BITS:literal, $DOC:literal) => {
		#[doc=$DOC]
		impl Entity for $INT {
			type StorageType = $INT;
			type VersionType = $INT_VERSION;

			fn new(idx: usize) -> Self {
				#[cfg(not(enrs_disable_asserts))]
				assert!(idx <= $INDEX_MASK);
				idx as Self::StorageType
			}

			#[allow(clippy::verbose_bit_mask)]
			fn is_null(self) -> bool {
				(self & $INDEX_MASK) == 0
			}

			fn idx(self) -> usize {
				(self & $INDEX_MASK) as usize
			}

			fn set_idx(&mut self, idx: usize) -> &mut Self {
				#[cfg(not(enrs_disable_asserts))]
				assert!(idx <= $INDEX_MASK);
				*self = (*self & $VERSION_MASK) | (idx as Self::StorageType);
				self
			}

			fn version(self) -> Self::VersionType {
				(self & $VERSION_MASK).wrapping_shr($SHIFT_BITS) as Self::VersionType
			}

			fn bump_version_with_idx(&mut self, idx: usize) {
				#[cfg(not(enrs_disable_asserts))]
				assert!(idx <= $INDEX_MASK);
				*self = ((*self & $VERSION_MASK).wrapping_shr($SHIFT_BITS) + 1)
					.wrapping_shl($SHIFT_BITS)
					+ (idx as Self::StorageType);
			}
		}
	};
}

unsigned_integral_entity!(
    u16,
    u8,
    0x0_FFF,
    0xF_000,
    12,
    "`u16` Entity, Index: 12 bits, Generation: 4 bits, Invalid ID: 0, Max: 4095"
);
unsigned_integral_entity!(
    u32,
    u16,
    0x000_FFFFF,
    0xFFF_00000,
    20,
    "`u32` Entity, Index: 20 bits, Generation: 12 bits, Invalid ID: 0, Max: 1048575"
);
unsigned_integral_entity!(
    u64,
    u32,
    0x00000000_FFFFFFFF,
    0xFFFFFFFF_00000000,
    32,
    "`u64` Entity, Index: 32 bits, Generation: 32 bits, Invalid ID: 0, Max: 4294967295"
);
// unsigned_integral_entity!(
//     u128,
//     u64,
//     0x00000000_00000000_FFFFFFFF_FFFFFFFF,
//     0xFFFFFFFF_FFFFFFFF_00000000_00000000,
//     64,
//     "`u64` Entity, Index: 32 bits, Generation: 32 bits, Invalid ID: 0, Max: 4294967295"
// );

#[macro_export]
macro_rules! delegate_wrapped_entity {
    ($SELF:ident, $INTERNAL:ident) => {
        impl Entity for $SELF {
            type StorageType = <$INTERNAL as Entity>::StorageType;
            type VersionType = <$INTERNAL as Entity>::VersionType;

            fn new(idx: usize) -> Self {
                $SELF(<$INTERNAL as Entity>::new(idx))
            }

            #[allow(clippy::verbose_bit_mask)]
            fn is_null(self) -> bool {
                self.0.is_null()
            }

            fn idx(self) -> usize {
                self.0.idx()
            }

            fn set_idx(&mut self, idx: usize) -> &mut Self {
                self.0.set_idx(idx);
                self
            }

            fn version(self) -> Self::VersionType {
                self.0.version()
            }

            fn bump_version_with_idx(&mut self, idx: usize) {
                self.0.bump_version_with_idx(idx)
            }
        }
    };
}

///// `u16` Entity, Index: 12 bits, Generation: 4 bits, Invalid ID: 0, Max: 4095
//impl Entity for u16 {
//	type StorageType = u16;
////	type VersionType = u8;
////	type DifferenceType = i32;
////	const ENTITY_MASK: Self::StorageType = 0x0FFF;
////	const VERSION_MASK: Self::StorageType = 0xF000;
////	const ENTITY_SHIFT: u32 = 4 * 3; // 3 is count of ENTITY_MASK F's
//	const NULL: Self = 0;
//	fn new(id: usize) -> Self {
//		debug_assert!(id <= 0x0FFF);
//		id as Self::StorageType
//	}
////	fn to_integral(self) -> Self::StorageType {
////		self
////	}
//	fn is_null(self) -> bool {
//		self.idx() == Self::NULL.idx()
//	}
////	fn id(self) -> Self::StorageType {
////		self & Self::ENTITY_MASK
////	}
////	fn idx(self) -> usize {
////		self.id() as usize
////	}
////	fn set_idx(&mut self, idx: usize) -> &mut Self {
////		*self = (idx as Self::StorageType & Self::ENTITY_MASK) + self.version().rotate_left(Self::ENTITY_SHIFT);
////		self
////	}
////	fn version(self) -> Self::StorageType {
////		(self & Self::VERSION_MASK).rotate_right(Self::ENTITY_SHIFT)
////	}
////	fn new_version(self, version: Self::StorageType) -> Self {
////		(version & Self::VERSION_MASK).rotate_left(Self::ENTITY_SHIFT) | self.id()
////	}
////	fn new_next_version(self) -> Self {
////		self.new_version(self.version() + 1)
////	}
//}
//
///// `u32` Entity, Index: 20 bits, Generation: 12 bits, Invalid ID: 0, Max: 1048575
//impl Entity for u32 {
//	type StorageType = u32;
////	type VersionType = u16;
////	type DifferenceType = i64;
////	const ENTITY_MASK: Self::StorageType = 0x000FFFFF;
////	const VERSION_MASK: Self::StorageType = 0xFFF00000;
////	const ENTITY_SHIFT: u32 = 4 * 5; // 5 is count of ENTITY_MASK F's
//	const NULL: Self = 0;
//	fn new(id: usize) -> Self {
//		debug_assert!(id <= 0x000FFFFF);
//		id as Self::StorageType
//	}
////	fn to_integral(self) -> Self::StorageType {
////		self
////	}
//	fn is_null(self) -> bool {
//		self.idx() == Self::NULL.idx()
//	}
////	fn id(self) -> Self::StorageType {
////		self & Self::ENTITY_MASK
////	}
////	fn idx(self) -> usize {
////		self.id() as usize
////	}
////	fn set_idx(&mut self, idx: usize) -> &mut Self {
////		*self = (idx as Self::StorageType & Self::ENTITY_MASK) + self.version().rotate_left(Self::ENTITY_SHIFT);
////		self
////	}
////	fn version(self) -> Self::StorageType {
////		(self & Self::VERSION_MASK).rotate_right(Self::ENTITY_SHIFT)
////	}
////	fn new_version(self, version: Self::StorageType) -> Self {
////		(version & Self::VERSION_MASK).rotate_left(Self::ENTITY_SHIFT) | self.id()
////	}
////	fn new_next_version(self) -> Self {
////		self.new_version(self.version() + 1)
////	}
//}
//
///// `u64` Entity, Index: 32 bits, Generation: 32 bits, Invalid ID: 0, Max: 4294967295
//impl Entity for u64 {
//	type StorageType = u64;
////	type VersionType = u32;
////	type DifferenceType = i128; // Should this be i64?  Hmm...
////	const ENTITY_MASK: Self::StorageType = 0x00000000FFFFFFFF;
////	const VERSION_MASK: Self::StorageType = 0xFFFFFFFF00000000;
////	const ENTITY_SHIFT: u32 = 4 * 8; // 8 is count of ENTITY_MASK F's
//	const NULL: Self = 0;
//	fn new(id: usize) -> Self {
//		debug_assert!(id <= 0x00000000FFFFFFFF);
//		id as Self::StorageType
//	}
////	fn to_integral(self) -> Self::StorageType {
////		self
////	}
//	fn is_null(self) -> bool {
//		self.idx() == Self::NULL.idx()
//	}
////	fn id(self) -> Self::StorageType {
////		self & Self::ENTITY_MASK
////	}
////	fn idx(self) -> usize {
////		self.id() as usize
////	}
////	fn set_idx(&mut self, idx: usize) -> &mut Self {
////		*self = (idx as Self::StorageType & Self::ENTITY_MASK) + self.version().rotate_left(Self::ENTITY_SHIFT);
////		self
////	}
////	fn version(self) -> Self::StorageType {
////		(self & Self::VERSION_MASK).rotate_right(Self::ENTITY_SHIFT)
////	}
////	fn new_version(self, version: Self::StorageType) -> Self {
////		(version & Self::VERSION_MASK).rotate_left(Self::ENTITY_SHIFT) | self.id()
////	}
////	fn new_next_version(self) -> Self {
////		self.new_version(self.version() + 1)
////	}
//}
