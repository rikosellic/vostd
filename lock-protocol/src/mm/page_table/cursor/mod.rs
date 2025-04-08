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
use vstd::tokens::SetToken;

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
    pte_index, KernelMode, PageTable, PageTableEntryTrait, PageTableError, PageTableMode,
    PagingConsts, PagingConstsTrait, PagingLevel, UserMode,
};

use crate::spec::simple_page_table;
use crate::exec;

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
    // #[expect(dead_code)]
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

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    pub(in crate::mm) fn move_forward(&mut self)
    requires
        old(self).va < MAX_USERSPACE_VADDR,
    ensures
        self.path == old(self).path,
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
    fn push_level(&mut self, child_pt: PTL, old_level: Tracked<PagingLevel>)
    requires
        old(self).level > 1,
        old(self).path.len() >= old(self).level as usize,
        old(self).path[old(self).level as usize - 1].is_some(),
        old_level@ >= old(self).level,
    ensures
        self.level == old(self).level - 1,
        self.path.len() == old(self).path.len(),
        self.path[old(self).level as usize - 1].is_some(),
        self.path[old(self).level as usize - 2].is_some(),
        old(self).va == self.va,
        old(self).barrier_va == self.barrier_va,
        old(self).path.len() == self.path.len(),
        old(self).path@.len() == self.path@.len(),
        old(self).path[old(self).level as usize - 1] == self.path[old(self).level as usize - 1],
        forall |i: int| 0 <= i < old(self).path.len() && i != old(self).level as usize - 2
                // path remains unchanged except the one being set
                ==> self.path[i] == old(self).path[i],
        self.path[old(self).level as usize - 1] == old(self).path[old(self).level as usize - 1],
        self.path@[old(self).level as usize - 1] == old(self).path@[old(self).level as usize - 1],
        self.path[old(self).level as usize - 2] == Some(child_pt),
        self.path.len() >= old_level@ ==>
            self.path[old_level@ as usize - 1] == old(self).path[old_level@ as usize - 1],
    {
        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level()); // TODO: assert

        // let old = self.path[self.level as usize - 1].replace(child_pt);
        let old = self.path.set(self.level as usize - 1, Some(child_pt));
    }

    // fn cur_entry(&mut self) -> Entry<'_, E, C> {
    fn cur_entry(&self, mock_page_table: &exec::MockPageTable,
                        ptes: Tracked<simple_page_table::SimplePageTable::ptes>)
                            -> (res: (Entry<'_, E, C, PTL>, Tracked<simple_page_table::SimplePageTable::ptes>))
    requires
        self.level > 0,
        self.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
        self.path.len() >= self.level as usize,
        self.path[self.level as usize - 1].is_some(),
        // mock_page_table.frames@.value().contains_key(self.path[self.level as usize - 1].unwrap().paddr() as int),
    ensures
        // res.1 == frames,
        res.1 == ptes,
        // mock_page_table.frames@.instance_id() == 
    {
        // let node = self.path[self.level as usize - 1].as_mut().unwrap();
        // node.entry(pte_index::<C>(self.va, self.level))

        let cur_node = self.path[self.level as usize - 1].as_ref().unwrap(); // current node
        // node.entry(pte_index(self.va, self.level))
        let res = Entry::new_at(cur_node, pte_index(self.va, self.level));
        (res, ptes)
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

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr {
        self.0.virt_addr()
    }

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

        // ghost
        instance: Tracked<simple_page_table::SimplePageTable::Instance>,
        unused_addrs: Tracked<SetToken<builtin::int, simple_page_table::SimplePageTable::unused_addrs>>,
        mut ptes_token: Tracked<simple_page_table::SimplePageTable::ptes>,
        unused_pte_addrs: Tracked<SetToken<builtin::int, simple_page_table::SimplePageTable::unused_pte_addrs>>,
        mock_page_table: &mut exec::MockPageTable,
    ) -> (res: Option<Frame<T>>)
    requires
        0 <= old(self).0.va < MAX_USERSPACE_VADDR,
        old(self).0.va < old(self).0.barrier_va.end,
        old(self).0.va + frame.size() <= old(self).0.barrier_va.end,
        1 < old(self).0.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
        old(self).0.path.len() >= old(self).0.level as usize,
        old(self).0.path.len() == PagingConsts::NR_LEVELS_SPEC() as usize,
        old(self).0.path[old(self).0.level as usize - 1].is_some(),
        instance@.id() == old(mock_page_table).frames@.instance_id(),
        instance@.id() == ptes_token@.instance_id(),
        instance@.id() == unused_addrs@.instance_id(),
        instance@.id() == unused_pte_addrs@.instance_id(),

        // path valid
        forall |i: int, j: int| 1 <= i < j < old(self).0.path.len() ==>
            0 < (j - 1)  < PagingConsts::NR_LEVELS_SPEC() &&
            #[trigger] old(self).0.path[i].is_some() ==>
                old(self).0.path[j].is_some() &&
                exec::get_pte_from_addr(
                    (#[trigger] old(self).0.path[j].unwrap().paddr() +
                        pte_index(old(self).0.va, (j - 1) as u8) * exec::SIZEOF_PAGETABLEENTRY) as usize).paddr()
                    == old(self).0.path[i].unwrap().paddr(),

        // path valid
        forall |i: int| 1 <= i < old(self).0.path.len() && old(self).0.path[i].is_some() ==>
            old(mock_page_table).frames@.value().contains_key(
                (#[trigger] old(self).0.path[i].unwrap().paddr() as int)
            ),
        old(mock_page_table).wf(),
    ensures
        self.0.path.len() == old(self).0.path.len(),
        forall |i: int| 1 < i <= old(self).0.level ==> #[trigger] self.0.path[i - 1].is_some(),
        self.0.path[old(self).0.level - 1] == old(self).0.path[old(self).0.level - 1],
        mock_page_table.frames@.instance_id() == instance@.id(),
        mock_page_table.wf(),
    {
        let end = self.0.va + frame.size();
        // assert!(end <= self.0.barrier_va.end); // TODO
        assert(self.0.path[old(self).0.level - 1].is_some());
        let old_level = Tracked(self.0.level);
        assert(old_level == old(self).0.level);

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
            self.0.path.len() == old(self).0.path.len(),
            self.0.va == old(self).0.va,
            forall |i: int| self.0.level - 1 <= i < old(self).0.level ==> self.0.path[i].is_some(),
            old(self).0.path.len() >= old(self).0.level as usize,
            1 < old(self).0.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
            self.0.path[old(self).0.level - 1].is_some(),
            self.0.va < MAX_USERSPACE_VADDR,
            self.0.path[old(self).0.level - 1] == old(self).0.path[old(self).0.level - 1],
            old_level@ == old(self).0.level,
            old_level@ >= self.0.level,
            mock_page_table.frames@.instance_id() == instance@.id(),
            ptes_token@.instance_id() == instance@.id(),
            // mock_page_table.frames@.value().contains_key(self.0.path[self.0.level as usize - 1].unwrap().paddr() as int),
        {
            // debug_assert!(should_map_as_tracked::<M>(self.0.va)); // TODO
            let cur_level = self.0.level;
            let cur_entry: Entry<'_, E, C, PTL>;
            let res = self.0.cur_entry(mock_page_table, ptes_token); // TODO: why we cannot copy frames and ptes_token?
            cur_entry = res.0;
            // assert(mock_page_table.frames == res.1);
            // assert(ptes_token == res.2);
            // mock_page_table.frames = res.1;
            ptes_token = res.1;
            assert(self.0.path[cur_level - 1].is_some());
            match cur_entry.to_ref::<T>() {
                Child::PageTableRef(pt) => {
                    // assert(ptes@.value().contains_key(pt as int));

                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0
                        .push_level(
                            // unsafe { PageTableLock::from_raw_paddr(pt) }
                            PTL::from_raw_paddr(pt),
                            old_level
                        );
                    assert(self.0.va == old(self).0.va);
                    assert(self.0.path@.len() == old(self).0.path@.len());
                    assert(self.0.path[cur_level - 2].is_some());
                    assert(self.0.path[old(self).0.level - 1].is_some());
                    assert(self.0.path[old_level@ - 1] == old(self).0.path[old_level@ - 1]);
                }
                Child::PageTable(_) => {
                    // unreachable!();
                    assert(false);
                }
                Child::None => {
                    let preempt_guard = crate::task::disable_preempt();
                    let pt = zeroed_pt_pool::alloc::<E, C, PTL>(
                        &preempt_guard,
                        cur_level - 1,
                        MapTrackingStatus::Tracked,
                    ); // alloc frame here
                    let paddr = pt.into_raw_paddr();
                    // SAFETY: It was forgotten at the above line.
                    let _ = cur_entry
                        .replace(Child::<E, C, T>::PageTable(
                            // unsafe { PageTableNode::from_raw(paddr) }
                            PageTableNode::from_raw(paddr)
                        )); // alloc pte here
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0
                        .push_level(
                            // unsafe { PageTableLock::from_raw_paddr(paddr) }
                            PTL::from_raw_paddr(paddr),
                            old_level
                        );
                    assert(self.0.path[cur_level - 1].is_some());
                    assert(self.0.path[cur_level - 2].is_some());
                    // assert(self.0.path[old(self).0.level - 1] == old(self).0.path[old(self).0.level - 1]);
                }
                Child::Frame(_, _) => {
                    // panic!("Mapping a smaller frame in an already mapped huge page");
                    assert(false);
                }
                Child::Untracked(_, _, _) => {
                    // panic!("Mapping a tracked page in an untracked range");
                    assert(false);
                }
                Child::Token(_) => {
                    // let split_child = cur_entry.split_if_huge_token().unwrap();
                    // self.0.push_level(split_child);
                    assert(false); // TODO: Token
                }
            }
            assert(self.0.level == cur_level - 1);
            assert(self.0.path[cur_level - 1].is_some());
            assert(self.0.path[self.0.level as usize - 1].is_some());
            continue;
        }
        assert(forall |i: int| 1 < i <= old(self).0.level ==> #[trigger] self.0.path[i - 1].is_some());
        assert(self.0.level == frame.map_level());

        // Map the current page.
        let old = self.0.cur_entry(mock_page_table, ptes_token).0.replace(Child::Frame(frame, prop));
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
