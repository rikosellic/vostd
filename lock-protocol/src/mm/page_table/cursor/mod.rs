mod locking;

use std::{
    any::TypeId,
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    char::MAX,
    marker::PhantomData,
    ops::Range,
};

use vstd::{invariant, layout::is_power_2, pervasive::VecAdditionalExecFns, prelude::*};
use vstd::bits::*;

use crate::{
    helpers::align_ext::align_down,
    mm::{
        child::Child, entry::Entry, frame, meta::AnyFrameMeta, node::PageTableNode,
        page_prop::PageProperty, page_size, page_table::zeroed_pt_pool, vm_space::Token, Frame,
        MapTrackingStatus, Paddr, PageTableLockTrait, Vaddr, MAX_USERSPACE_VADDR, PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::VMALLOC_VADDR_RANGE,
};

use super::{
    node::PageTableLock, pte_index, KernelMode, PageTable, PageTableEntryTrait, PageTableError,
    PageTableMode, PagingConsts, PagingConstsTrait, PagingLevel, UserMode,
};

verus! {
/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
// #[derive(Debug)] // TODO: Implement `Debug` for `Cursor`.
pub struct Cursor<'a, M: PageTableMode, E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    // path: [Option<PageTableLock<E, C, T>>; MAX_NR_LEVELS],
    pub path: Vec<Option<PTL>>,
    /// The level of the page table that the cursor currently points to.
    pub level: PagingLevel,
    /// The top-most level that the cursor is allowed to access.
    ///
    /// From `level` to `guard_level`, the nodes are held in `path`.
    pub guard_level: PagingLevel,
    /// The virtual address that the cursor currently points to.
    pub va: Vaddr,
    /// The virtual address range that is locked.
    pub barrier_va: Range<Vaddr>,
    /// This also make all the operation in the `Cursor::new` performed in a
    /// RCU read-side critical section.
    #[expect(dead_code)]
    pub preempt_guard: DisabledPreemptGuard,
    // _phantom: PhantomData<&'a PageTable<M, E, C>>,
    pub _phantom: PhantomData<&'a PageTable<M, E, C>>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
const MAX_NR_LEVELS: usize = 4;

// #[derive(Clone, Debug)] // TODO: Implement Debug and Clone for PageTableItem
pub enum PageTableItem<T: AnyFrameMeta> {
    NotMapped {
        va: Vaddr,
        len: usize,
    },
    Mapped {
        va: Vaddr,
        page: Frame<T>,
        prop: PageProperty,
    },
    MappedUntracked {
        va: Vaddr,
        pa: Paddr,
        len: usize,
        prop: PageProperty,
    },
    StrayPageTable {
        pt: Frame<T>,
        va: Vaddr,
        len: usize,
    },
    /// The current slot is marked to be reserved.
    Marked {
        /// The virtual address of the slot.
        va: Vaddr,
        /// The length of the slot.
        len: usize,
        /// A user-provided token.
        token: Token,
    },
}

impl<'a, M: PageTableMode, E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>> Cursor<'a, M, E, C, PTL> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub fn new(pt: &'a PageTable<M, E, C>, va: &Range<Vaddr>) -> Result<Self, PageTableError> {
        if !M::covers(va)
            // || va.is_empty()
            || !(va.start < va.end)
            {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        // const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) }; // TODO
        let new_pt_is_tracked = if should_map_as_tracked::<M>(va.start) {
            MapTrackingStatus::Tracked
        } else {
            MapTrackingStatus::Untracked
        };
        Ok(locking::lock_range(pt, va, new_pt_is_tracked))
    }

    /// Gets the information of the current slot.
    // TODO
    // pub fn query<T: AnyFrameMeta>(&mut self) -> Result<PageTableItem<T>, PageTableError> {
    //     if self.va >= self.barrier_va.end {
    //         return Err(PageTableError::InvalidVaddr(self.va));
    //     }

    //     loop {
    //         let level = self.level;
    //         let va = self.va;

    //         match self.cur_entry().to_ref() {
    //             Child::PageTableRef(pt) => {
    //                 // SAFETY: `pt` points to a PT that is attached to a node
    //                 // in the locked sub-tree, so that it is locked and alive.
    //                 self.push_level(unsafe { PageTableLock::<E, C>::from_raw_paddr(pt) });
    //                 continue;
    //             }
    //             Child::PageTable(_) => {
    //                 // unreachable!();
    //                 // assert(false); // TODO
    //             }
    //             Child::None => {
    //                 return Ok(PageTableItem::NotMapped {
    //                     va,
    //                     len: page_size::<C>(level),
    //                 });
    //             }
    //             Child::Frame(page, prop) => {
    //                 return Ok(PageTableItem::Mapped { va, page, prop });
    //             }
    //             Child::Untracked(pa, plevel, prop) => {
    //                 // debug_assert_eq!(plevel, level); // TODO: assert
    //                 return Ok(PageTableItem::MappedUntracked {
    //                     va,
    //                     pa,
    //                     len: page_size::<C>(level),
    //                     prop,
    //                 });
    //             }
    //             Child::Token(token) => {
    //                 return Ok(PageTableItem::Marked {
    //                     va,
    //                     len: page_size::<C>(level),
    //                     token,
    //                 });
    //             }
    //         }
    //     }
    // }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    pub(in crate::mm) fn move_forward(&mut self)
    requires
        old(self).va < MAX_USERSPACE_VADDR,
    ensures
        self.path.len() == old(self).path.len(),
        self.level == old(self).level,
        self.va == old(self).va
    {
        // let page_size = page_size::<C>(self.level);
        // // let next_va = self.va.align_down(page_size) + page_size;
        // let next_va = align_down(self.va, page_size) + page_size;
        // while self.level < self.guard_level && pte_index(next_va, self.level) == 0 {
        //     self.pop_level();
        // }
        // self.va = next_va;
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    // TODO
    // pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError>
    // requires
    //     old(self).barrier_va.start < old(self).barrier_va.end,
    //     old(self).barrier_va.end < MAX_USERSPACE_VADDR,
    //     old(self).va >= old(self).barrier_va.start,
    //     old(self).va < old(self).barrier_va.end,
    //     old(self).level < PagingConsts::NR_LEVELS_SPEC(),
    //     old(self).level > 0,
    //     old(self).path.len() > old(self).level as usize,
    // {
    //     // assert!(va % C::BASE_PAGE_SIZE() == 0); // TODO
    //     // if !self.barrier_va.contains(&va) {
    //     //     return Err(PageTableError::InvalidVaddr(va));
    //     // }
    //     if va >= self.barrier_va.end || va < self.barrier_va.start {
    //         return Err(PageTableError::InvalidVaddr(va));
    //     }

    //     loop
    //     invariant
    //         0 < self.level < PagingConsts::NR_LEVELS_SPEC() as usize,
    //     {
    //         let cur_page_size = page_size::<C>(self.level + 1) as u64;
    //         let self_va = self.va as u64; // make verus happy
    //         let cur_node_start = self_va & !(cur_page_size - 1);
    //         assert(is_power_2(cur_page_size as int));
    //         let cur_page_size_minus_1 = cur_page_size - 1;
    //         assert(cur_node_start < self_va) by {
    //             assert(self_va & !cur_page_size_minus_1 <= cur_node_start) by (bit_vector);
    //         };
    //         let cur_node_end = cur_node_start as usize + page_size::<C>(self.level + 1);
    //         // If the address is within the current node, we can jump directly.
    //         if cur_node_start as usize <= va && va < cur_node_end {
    //             self.va = va;
    //             return Ok(());
    //         }

    //         // There is a corner case that the cursor is depleted, sitting at the start of the
    //         // next node but the next node is not locked because the parent is not locked.
    //         if self.va >= self.barrier_va.end && self.level == self.guard_level {
    //             self.va = va;
    //             return Ok(());
    //         }

    //         // debug_assert!(self.level < self.guard_level); // TODO
    //         self.pop_level();
    //     }
    // }

    pub fn virt_addr(&self) -> Vaddr {
        self.va
    }

    /// Goes up a level.
    fn pop_level(&mut self)
    requires
        old(self).level <= PagingConsts::NR_LEVELS_SPEC() as usize,
        old(self).level > 1,
        old(self).path.len() > old(self).level as usize,
    {
        // let Some(taken) = self.path[self.level as usize - 1].take() else {
        //     panic!("Popping a level without a lock");
        // };
        let taken = &self.path[self.level as usize - 1];
        if (taken.is_none()) {
            // panic!("Popping a level without a lock");
            // assert(false); // TODO
        }
        // let _taken = taken.unwrap().into_raw_paddr(); // TODO
        self.level = self.level + 1;
    }

    /// Goes down a level to a child page table.
    fn push_level(&mut self, child_pt: PTL)
    requires
        old(self).level > 1,
        old(self).path.len() >= old(self).level as usize,
    ensures
        self.level == old(self).level - 1,
        self.path.len() == old(self).path.len(),
        self.path[self.level as usize - 1].is_some(),
        old(self).va == self.va,
        old(self).barrier_va == self.barrier_va,
        old(self).path.len() == self.path.len(),
        old(self).path@.len() == self.path@.len(),
    {
        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level()); // TODO: assert

        // let old = self.path[self.level as usize - 1].replace(child_pt);
        let old = self.path.set(self.level as usize - 1, Some(child_pt));
        // debug_assert!(old.is_none()); // TODO
    }

    // fn cur_entry(&mut self) -> Entry<'_, E, C> {
    fn cur_entry(&self) -> Entry<'_, E, C, PTL>
    requires
        self.level > 0,
        self.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
        self.path.len() >= self.level as usize,
        self.path[self.level as usize - 1].is_some(),
    {
        // let node = self.path[self.level as usize - 1].as_mut().unwrap();
        // node.entry(pte_index::<C>(self.va, self.level))

        let node = self.path[self.level as usize - 1].as_ref().unwrap();
        // node.entry(pte_index(self.va, self.level))
        Entry::new_at(node, pte_index(self.va, self.level))
    }
}


/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
// #[derive(Debug)] // TODO: Implement `Debug` for `CursorMut`.
pub struct CursorMut<'a, M: PageTableMode, E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>>(
    pub Cursor<'a, M, E, C, PTL>,
);
impl<'a, M: PageTableMode, E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>> CursorMut<'a, M, E, C, PTL> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub(super) fn new(
        pt: &'a PageTable<M, E, C>,
        va: &Range<Vaddr>,
    ) -> Result<Self, PageTableError> {
        Cursor::new(pt, va).map(|inner| Self(inner))
    }

    /// Jumps to the given virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    ///
    /// # Panics
    ///
    /// This method panics if the address is out of the range where the cursor is required to operate,
    /// or has bad alignment.
    // TODO
    // pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
    //     self.0.jump(va)
    // }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr {
        self.0.virt_addr()
    }

    /// Gets the information of the current slot.
    // TODO
    // pub fn query<T: AnyFrameMeta>(&mut self) -> Result<PageTableItem<T>, PageTableError> {
    //     self.0.query()
    // }

    /// Maps the range starting from the current address to a [`Frame<dyn AnyFrameMeta>`].
    ///
    /// It returns the previously mapped [`Frame<dyn AnyFrameMeta>`] if that exists.
    ///
    /// # Panics
    ///
    /// This function will panic if
    ///  - the virtual address range to be mapped is out of the range;
    ///  - the alignment of the page is not satisfied by the virtual address;
    ///  - it is already mapped to a huge page while the caller wants to map a smaller one.
    ///
    /// # Safety
    ///
    /// The caller should ensure that the virtual range being mapped does
    /// not affect kernel's memory safety.
    pub fn map<T: AnyFrameMeta>(
        &mut self,
        frame: Frame<T>,
        prop: PageProperty,
    ) -> (res: Option<Frame<T>>)
    requires
        0 <= old(self).0.va < MAX_USERSPACE_VADDR,
        old(self).0.va < old(self).0.barrier_va.end,
        old(self).0.va + frame.size() <= old(self).0.barrier_va.end,
        1 < old(self).0.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
        old(self).0.path.len() >= old(self).0.level as usize,
        old(self).0.path[old(self).0.level as usize - 1].is_some(),
    ensures
        self.0.path.len() == old(self).0.path.len(),
    {
        let end = self.0.va + frame.size();
        // assert!(end <= self.0.barrier_va.end); // TODO

        // Go down if not applicable.
        while self.0.level > frame.map_level()
            // || self.0.va % page_size::<C>(self.0.level) != 0 // TODO?
            // || self.0.va + page_size::<C>(self.0.level) > end // TODO?
        invariant
            // self.0.va + page_size::<C>(self.0.level) <= end,
            self.0.level >= frame.map_level(),
            1 <= self.0.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
            self.0.path.len() >= self.0.level as usize,
            self.0.path[self.0.level as usize - 1].is_some(),
            self.0.va < MAX_USERSPACE_VADDR,
            self.0.path.len() == old(self).0.path.len(),
            self.0.va == old(self).0.va,
        {
            // debug_assert!(should_map_as_tracked::<M>(self.0.va)); // TODO
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry();
            match cur_entry.to_ref::<T>() {
                Child::PageTableRef(pt) => {
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0
                        .push_level(
                            // unsafe { PageTableLock::from_raw_paddr(pt) }
                            PTL::from_raw_paddr(pt)
                        );
                    assert(self.0.va == old(self).0.va);
                    assert(self.0.path@.len() == old(self).0.path@.len());
                }
                Child::PageTable(_) => {
                    // unreachable!();
                    // assert(false); // TODO: We need to assert the child cannot be a page table.
                }
                Child::None => {
                    let preempt_guard = crate::task::disable_preempt();
                    let pt = zeroed_pt_pool::alloc::<E, C, PTL>(
                        &preempt_guard,
                        cur_level - 1,
                        MapTrackingStatus::Tracked,
                    );
                    let paddr = pt.into_raw_paddr();
                    // SAFETY: It was forgotten at the above line.
                    let _ = cur_entry
                        .replace(Child::<E, C, T>::PageTable(
                            // unsafe { PageTableNode::from_raw(paddr) }
                            PageTableNode::from_raw(paddr)
                        ));
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0
                        .push_level(
                            // unsafe { PageTableLock::from_raw_paddr(paddr) }
                            PTL::from_raw_paddr(paddr)
                        );
                }
                Child::Frame(_, _) => {
                    // panic!("Mapping a smaller frame in an already mapped huge page");
                    // assert(false); // TODO
                }
                Child::Untracked(_, _, _) => {
                    // panic!("Mapping a tracked page in an untracked range");
                    // assert(false); // TODO
                }
                Child::Token(_) => {
                    // let split_child = cur_entry.split_if_huge_token().unwrap();
                    // self.0.push_level(split_child);
                }
            }
            continue;
        }
        // debug_assert_eq!(self.0.level, frame.map_level()); // TODO: assert

        // Map the current page.
        let old = self.0.cur_entry().replace(Child::Frame(frame, prop));
        self.0.move_forward();

        match old {
            Child::Frame(old_page, _) => Some(old_page),
            Child::None | Child::Token(_) => None,
            Child::PageTable(_) => {
                // todo!("Dropping page table nodes while mapping requires TLB flush")
                // assert(false); // TODO
                None
            }
            Child::Untracked(_, _, _) => {
                // panic!("Mapping a tracked page in an untracked range"),
                // assert(false); // TODO
                None
            }
            // Child::PageTableRef(_) => unreachable!(),
            Child::PageTableRef(_) => {
                // panic!("Mapping a page in a page table reference")
                // assert(false); // TODO
                None
            }
        }
    }
}


fn should_map_as_tracked<M: PageTableMode>(va: Vaddr) -> bool {
    // TODO: Check if the type is `KernelMode` or `UserMode`.
    // (TypeId::of::<M>() == TypeId::of::<KernelMode>()
    //     || TypeId::of::<M>() == TypeId::of::<UserMode>())
    //     &&

    crate::x86_64::kspace::should_map_as_tracked(va)
}
}
