mod locking;
pub mod spec_helpers;

use std::{
    any::TypeId,
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    char::MAX,
    marker::PhantomData,
    ops::Range,
};

use vstd::{
    invariant, layout::is_power_2, pervasive::VecAdditionalExecFns, prelude::*,
    raw_ptr::MemContents,
};
use vstd::bits::*;
use vstd::tokens::SetToken;

use crate::{
    helpers::align_ext::align_down,
    mm::{
        child::Child, entry::Entry, frame, meta::AnyFrameMeta, node::PageTableNode,
        nr_subpage_per_huge, page_prop::PageProperty, page_size, vm_space::Token, Frame,
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
use spec_helpers::*;
use crate::mm::NR_ENTRIES;

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
        self.path[self.level as usize - 1] == Some(child_pt),
        self.path[self.level as usize - 1].unwrap().paddr() as int == child_pt.paddr() as int,
        self.path[path_index_at_level(self.level)].unwrap().paddr() as int == child_pt.paddr() as int,
    {
        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level()); // TODO: assert

        // let old = self.path[self.level as usize - 1].replace(child_pt);
        let old = self.path.set(self.level as usize - 1, Some(child_pt));
    }

    // fn cur_entry(&mut self) -> Entry<'_, E, C> {
    fn cur_entry(&self, mpt: &exec::MockPageTable)
                            -> (res: Entry<'_, E, C, PTL>)
    requires
        self.level > 0,
        self.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
        self.path.len() >= self.level as usize,
        self.path[self.level as usize - 1].is_some(),
        mpt.wf(),
        // mock_page_table.frames@.value().contains_key(self.path[self.level as usize - 1].unwrap().paddr() as int),
    ensures
        res.pte.pte_paddr() == self.path[self.level as usize - 1].unwrap().paddr() as usize +
                                pte_index(self.va, self.level) * exec::SIZEOF_PAGETABLEENTRY,
        res.pte.pte_paddr() == exec::get_pte_from_addr(res.pte.pte_paddr(), mpt).pte_addr,
        res.pte.frame_paddr() == exec::get_pte_from_addr(res.pte.pte_paddr(), mpt).frame_pa,
        res.idx == pte_index(self.va, self.level),
        res.idx < nr_subpage_per_huge(),
        res.pte.frame_paddr() == 0 ==> !mpt.ptes@.value().contains_key(res.pte.pte_paddr() as int),
        res.pte.frame_paddr() != 0 ==> mpt.ptes@.value().contains_key(res.pte.pte_paddr() as int),
    {
        // let node = self.path[self.level as usize - 1].as_mut().unwrap();
        // node.entry(pte_index::<C>(self.va, self.level))

        let cur_node = self.path[self.level as usize - 1].as_ref().unwrap(); // current node
        // node.entry(pte_index(self.va, self.level))
        let res = Entry::new_at(cur_node, pte_index(self.va, self.level), mpt);
        res
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

    pub open spec fn path_valid_before_map(&self) -> bool {
        &&& self.0.path.len() >= self.0.level
        &&& self.0.path.len() == PagingConsts::NR_LEVELS_SPEC()
        &&& self.0.path[self.0.level - 1].is_some()
    }

    pub open spec fn path_valid_after_map(&self, old: &CursorMut<'a, M, E, C, PTL>) -> bool {
        &&& self.0.path.len() == old.0.path.len()
        &&& self.0.path.len() == PagingConsts::NR_LEVELS_SPEC()
        &&& self.0.path[self.0.level - 1].is_some()
        &&& self.0.path[old.0.level - 1] == old.0.path[old.0.level - 1]
        &&& forall |i: int| 1 < i <= old.0.level ==> #[trigger] self.0.path[i - 1].is_some()
    }

    pub open spec fn va_valid<T: AnyFrameMeta>(&self, frame: Frame<T>, old: Option<&CursorMut<'a, M, E, C, PTL>>) -> bool {
        &&& self.0.va < MAX_USERSPACE_VADDR
        &&& self.0.va >= self.0.barrier_va.start
        &&& self.0.va + frame.size() <= self.0.barrier_va.end
        &&& !old.is_none() ==> self.0.va == old.unwrap().0.va
    }

    pub open spec fn path_wf(&self, mock_page_table: &exec::MockPageTable) -> bool {
        &&& forall |i: int, j: int| 1 <= i < j < self.0.path.len() ==>
                0 < (j - 1)  < PagingConsts::NR_LEVELS_SPEC() &&
                #[trigger] self.0.path[i].is_some() ==>
                    self.0.path[j].is_some() &&
                    exec::get_pte_from_addr(
                        (#[trigger] self.0.path[j].unwrap().paddr() +
                            pte_index(self.0.va, (j + 1) as u8) * exec::SIZEOF_PAGETABLEENTRY) as usize,
                            mock_page_table).frame_paddr()
                        == self.0.path[i].unwrap().paddr()
        &&& forall |i: int| 1 <= i < self.0.path.len() && self.0.path[i].is_some() ==>
                mock_page_table.frames@.value().contains_key(
                    (#[trigger] self.0.path[i].unwrap().paddr() as int)
                )
    }

    pub open spec fn mock_page_table_valid_before_map(&self, mock_page_table: &exec::MockPageTable) -> bool {
        &&& mock_page_table.wf()
        &&& mock_page_table.frames@.value().contains_key(self.0.path[self.0.level as usize - 1].unwrap().paddr() as int)
    }

    pub open spec fn mock_page_table_valid_after_map(&self, mock_page_table: &exec::MockPageTable) -> bool {
        &&& mock_page_table.wf()
        &&& mock_page_table.frames@.value().contains_key(self.0.path[self.0.level as usize - 1].unwrap().paddr() as int)
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
        tokens: Tracked<exec::Tokens>,

        // non ghost
        mpt: &mut exec::MockPageTable,
        cur_alloc_index: &mut usize,
    ) -> (res: Option<Frame<T>>)
    requires
        instance_match(old(mpt), tokens@),

        // cursor validation
        old(self).va_valid(frame, None),
        level_is_greate_than_one(old(self).0.level),
        old(self).path_valid_before_map(),

        old(self).path_wf(old(mpt)),

        *old(cur_alloc_index) < exec::MAX_FRAME_NUM - 4, // we have enough frames

        // page table validation
        old(self).mock_page_table_valid_before_map(old(mpt)),
        mpt_and_tokens_wf(old(mpt), tokens@),
        mpt_not_contains_not_allocated_frames(old(mpt), *old(cur_alloc_index)),
        unallocated_frames_are_unused(tokens@.unused_addrs, tokens@.unused_pte_addrs,*old(cur_alloc_index)),
        tokens_wf(tokens@.unused_addrs, tokens@.unused_pte_addrs),
    ensures
        self.path_valid_after_map(old(self)),
        instance_match(old(mpt), tokens@),
        mpt.wf(),
        *cur_alloc_index < exec::MAX_FRAME_NUM, // we have enough frames
        self.mock_page_table_valid_after_map(mpt),
    {
        let end = self.0.va + frame.size();
        let old_level = Tracked(self.0.level);
        assert(old_level == old(self).0.level);

        let tracked exec::Tokens {
            unused_addrs: mut unused_addrs,
            unused_pte_addrs: mut unused_pte_addrs,
        } = tokens.get(); // TODO: can we just use the tokens inside the loop?

        #[verifier::loop_isolation(false)]
        // Go down if not applicable.
        while self.0.level > frame.map_level()
            // || self.0.va % page_size::<C>(self.0.level) != 0 // TODO?
            // || self.0.va + page_size::<C>(self.0.level) > end // TODO?
        invariant
            // self.0.va + page_size::<C>(self.0.level) <= end,
            self.0.level >= frame.map_level(),
            self.0.path.len() == old(self).0.path.len(),
            self.va_valid(frame, Some(old(self))),
            forall |i: int| path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                            ==> self.0.path[i].is_some(),
            self.0.path[path_index_at_level(old_level@)] == old(self).0.path[path_index_at_level(old_level@)],
            old_level@ >= self.0.level,
            mpt.wf(),
            *cur_alloc_index < exec::MAX_FRAME_NUM - 4, // we have enough frames
            instance_match_addrs(mpt, unused_addrs, unused_pte_addrs),
            forall |i: int| path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level) ==>
                #[trigger] mpt.frames@.value().contains_key(self.0.path[i].unwrap().paddr() as int),
            mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index),
            unallocated_frames_are_unused(unused_addrs, unused_pte_addrs, *cur_alloc_index),
            tokens_wf(unused_addrs, unused_pte_addrs),
        {
            // debug_assert!(should_map_as_tracked::<M>(self.0.va)); // TODO
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(mpt);
            match cur_entry.to_ref::<T>(mpt) {
                Child::PageTableRef(pt) => {
                    assert(mpt.frames@.value().contains_key(pt as int));
                    assert(cur_entry.pte.frame_paddr() != 0);

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

                    assert(mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index));
                    assert(forall |i: int| path_index_at_level(self.0.level) <= i <= path_index_at_level(old_level@) ==>
                        #[trigger] mpt.frames@.value().contains_key(self.0.path[i].unwrap().paddr() as int));
                }
                Child::PageTable(_) => {
                    // unreachable!();
                    assert(false);
                }
                Child::None => {
                    assert(!mpt.ptes@.value().contains_key(cur_entry.pte.pte_paddr() as int));
                    assert(cur_entry.pte.frame_paddr() == 0);
                    assert(mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index));

                    let preempt_guard = crate::task::disable_preempt(); // currently nothing happen

                    let used_addr = exec::frame_index_to_addr(*cur_alloc_index);
                    let tracked used_addr_token = unused_addrs.tracked_remove(used_addr as int);
                    assert(used_addr_token.instance_id() == mpt.instance@.id());

                    // before_alloc
                    {
                        assert(used_addr_token.element() == used_addr as int); // ensured by token_wf
                        assert(!mpt.frames@.value().contains_key(used_addr as int)); // ensured by unallocated_frames_are_unused
                        assert(mpt.mem@[*cur_alloc_index].1@.mem_contents() == MemContents::<exec::SimpleFrame>::Uninit);
                        assert(forall |i: int| 0 <= i < NR_ENTRIES ==>
                                ! (#[trigger] mpt.ptes@.value().dom().contains(used_addr + i * exec::SIZEOF_PAGETABLEENTRY)));
                        assert(forall |i: int| 0 <= i < NR_ENTRIES ==>
                                ! #[trigger] mpt.ptes@.value().contains_key(used_addr + i * exec::SIZEOF_PAGETABLEENTRY as int));
                        assert(forall |i: int| #[trigger] mpt.ptes@.value().contains_key(i) ==>
                                (mpt.ptes@.value()[i]).frame_pa != used_addr);
                    }
                    let pt = PTL::alloc(
                        cur_level - 1,
                        MapTrackingStatus::Tracked,

                        mpt,
                        *cur_alloc_index,
                        used_addr,
                        Tracked(used_addr_token), // TODO: can we pass all the tokens directly?
                    ); // alloc frame here
                    *cur_alloc_index += 1; // TODO: do it inside the alloc function

                    let paddr = pt.into_raw_paddr();

                    // SAFETY: It was forgotten at the above line.
                    let _ = cur_entry
                        .replace(Child::<E, C, T>::PageTable(
                            // unsafe { PageTableNode::from_raw(paddr) }
                            PageTableNode::from_raw(paddr)
                        ), mpt, self.0.level); // alloc pte here
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0
                        .push_level(
                            // unsafe { PageTableLock::from_raw_paddr(paddr) }
                            PTL::from_raw_paddr(paddr),
                            old_level
                        );
                    assert(*cur_alloc_index < exec::MAX_FRAME_NUM - 4) by { admit(); }; // TODO: P0

                    assume(mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index)); // TODO: P0
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

        let cur_entry = self.0.cur_entry(mpt);
        assert(cur_entry.idx < nr_subpage_per_huge() as usize) by { admit(); } // TODO
        // Map the current page.
        let old_entry = cur_entry.replace(Child::Frame(frame, prop), mpt, self.0.level);
        self.0.move_forward();

        // TODO: P0
        assume(forall |i: int| path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level) ==>
                #[trigger] mpt.frames@.value().contains_key(self.0.path[i].unwrap().paddr() as int));

        match old_entry {
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
