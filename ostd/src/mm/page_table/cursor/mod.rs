// SPDX-License-Identifier: MPL-2.0
//! The page table cursor for mapping and querying over the page table.
//!
//! # The page table lock protocol
//!
//! We provide a fine-grained ranged mutual-exclusive lock protocol to allow
//! concurrent accesses to non-overlapping virtual ranges in the page table.
//!
//! [`CursorMut::new`] will lock a range in the virtual space and all the
//! operations on the range with the cursor will be atomic as a transaction.
//!
//! The guarantee of the lock protocol is that, if two cursors' ranges overlap,
//! all of one's operation must be finished before any of the other's
//! operation. The order depends on the scheduling of the threads. If a cursor
//! is ordered after another cursor, it will see all the changes made by the
//! previous cursor.
//!
//! The implementation of the lock protocol resembles two-phase locking (2PL).
//! [`CursorMut::new`] accepts an address range, which indicates the page table
//! entries that may be visited by this cursor. Then, [`CursorMut::new`] finds
//! an intermediate page table (not necessarily the last-level or the top-
//! level) which represents an address range that fully contains the whole
//! specified address range. Then it locks all the nodes in the sub-tree rooted
//! at the intermediate page table node, with a pre-order DFS order. The cursor
//! will only be able to access the page table entries in the locked range.
//! Upon destruction, the cursor will release the locks in the reverse order of
//! acquisition.
mod locking;

use vstd::{arithmetic::power2::pow2, math::abs, prelude::*, simple_pptr::*};
use vstd_extra::{
    arithmetic::*, assert, assert_eq, drop_tracking::TrackDrop, ghost_tree::*, ownership::*,
    panic::*,
};

use crate::specs::mm::{
    frame::{
        mapping::{frame_to_index, index_to_meta, max_meta_slots, meta_to_index},
        meta_owners::{FracMetadataPerm, MetaSlotOwner, PageUsage, is_mmio_paddr},
        meta_region_owners::MetaRegionOwners,
    },
    page_table::{
        cursor::page_size_lemmas::*, mapping_set_lemmas::lemma_extend_empty_mapping_range,
    },
};

use super::{
    Child, ChildRef, Entry, EntryOwner, PageTable, PageTableConfig, PageTableError, PageTableGuard,
    PageTablePageMeta, PagingConstsTrait, PagingLevel, pte_index,
};
use crate::arch::mm::PagingConsts;
use crate::mm::frame::meta::{
    META_SLOT_SIZE, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED, mapping::frame_to_meta,
};
use crate::mm::frame::{AnyFrameMeta, Frame};
use crate::mm::page_table::*;
use crate::mm::{MAX_PADDR, Paddr, Vaddr, page_size};
use crate::{
    mm::{page_prop::PageProperty, page_table::is_valid_range},
    specs::task::InAtomicMode,
};
use align_ext::AlignExt;
use core::{fmt::Debug, marker::PhantomData, mem::ManuallyDrop, ops::Range};

verus! {

broadcast use group_ghost_tree_lemmas;

/// The state of virtual pages represented by a page table.
///
/// This is the return type of the [`Cursor::query`] method.
pub type PagesState<C> = (Range<Vaddr>, Option<<C as PageTableConfig>::Item>);

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
pub struct Cursor<'rcu, C: PageTableConfig, A: InAtomicMode> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PageTableGuard<'rcu, C>>; MAX_NR_LEVELS],
    /// The cursor should be used in a RCU read side critical section.
    pub rcu_guard: &'rcu A,
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
    pub _phantom: PhantomData<&'rcu PageTable<C>>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
const MAX_NR_LEVELS: usize = 4;

/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
pub struct CursorMut<'rcu, C: PageTableConfig, A: InAtomicMode>(pub Cursor<'rcu, C, A>);

impl<C: PageTableConfig, A: InAtomicMode> Iterator for Cursor<'_, C, A> {
    type Item = PagesState<C>;

    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}

/// Reborrow the inner `PageTableGuard` of `path[idx]` (which must be `Some`).
#[verus_spec(res =>
    requires
        idx < NR_LEVELS,
        old(path)[idx as int] is Some,
    ensures
        *res == old(path)[idx as int]->0,
        final(path)[idx as int] is Some,
        final(path)[idx as int]->0 == *final(res),
        forall |i: int| 0 <= i < NR_LEVELS && i != idx ==>
            #[trigger] final(path)[i] == old(path)[i],
)]
fn path_slot_as_mut<'a, 'rcu, C: PageTableConfig>(
    path: &'a mut [Option<PageTableGuard<'rcu, C>>; NR_LEVELS],
    idx: usize,
) -> &'a mut PageTableGuard<'rcu, C> {
    path[idx].as_mut().unwrap()
}

/// A fragment of a page table that can be taken out of the page table.
pub enum PageTableFrag<C: PageTableConfig> {
    /// A mapped page table item.
    Mapped { va: Vaddr, item: C::Item },
    /// A sub-tree of a page table that is taken out of the page table.
    ///
    /// The caller is responsible for dropping it after TLB coherence.
    StrayPageTable { pt: Frame<dyn AnyFrameMeta>, va: Vaddr, len: usize, num_frames: usize },
}

impl<C: PageTableConfig> PageTableFrag<C> {
    #[cfg(ktest)]
    pub fn va_range(&self) -> Range<Vaddr> {
        match self {
            PageTableFrag::Mapped { va, item } => {
                let (pa, level, prop) = C::item_into_raw(item.clone());
                // SAFETY: All the arguments match those returned from the previous call
                // to `item_into_raw`, and we are taking ownership of the cloned item.
                drop(unsafe { C::item_from_raw(pa, level, prop) });
                *va..*va + page_size::<C>(level)
            },
            PageTableFrag::StrayPageTable { va, len, .. } => *va..*va + *len,
        }
    }
}

/// Localizes the set arithmetic used when replacing the cursor's current subtree.
#[verifier::spinoff_prover]
proof fn lemma_replace_cur_entry_mapping_sets(
    all: Set<Mapping>,
    current: Set<Mapping>,
    replacement: Set<Mapping>,
    old_subtree: Set<Mapping>,
    new_subtree: Set<Mapping>,
)
    requires
        current.subset_of(all),
        old_subtree.subset_of(current),
        replacement == (current - old_subtree).union(new_subtree),
    ensures
        (all - current).union(replacement) == (all - old_subtree).union(new_subtree),
{
}

#[verus_verify]
impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Ghost(pa): Ghost<Paddr>,
        requires
            item.clone_requires(*old(regions)),
            C::item_into_raw(*item).0 == pa,
        ensures
            C::item_into_raw(res).0 == C::item_into_raw(*item).0,
            C::item_into_raw(res).1 == C::item_into_raw(*item).1,
            C::item_into_raw(res).2 == C::item_into_raw(*item).2,
            (C::item_into_raw(res).3@ is Some)
                == (C::item_into_raw(*item).3@ is Some),
            item.clone_ensures(*old(regions), *final(regions), res),
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
            C::item_into_raw(*item).3@ is Some ==> {
                old(regions).inc_frame_reference_region_spec(pa, *final(regions))
            },
            C::item_into_raw(*item).3@ is None ==> *final(regions) == *old(regions),
    )]
    pub fn clone_item(item: &C::Item) -> C::Item {
        let res = item.clone(Tracked(regions));
        proof {
            C::lemma_clone_ensures_concrete(*item, pa, *old(regions), *regions, res);
        }
        res
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<&'owner mut FlatPageTableOwner<C>>,
             Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            pt.relates_flat_owner(*old(pt_own), *old(regions)),
            old(pt_own).node(old(pt_own).root).node.relate_guard(root_guard),
            // Per-config tightening: e.g. `KernelPtConfig` overrides
            // `LOCKED_END_BOUND_spec` to `FRAME_METADATA_BASE_VADDR`. Callers
            // for `KernelPtConfig` (KVirtArea, etc.) discharge this from the
            // `kvirt_alloc_range_bounds` axiom; default-config callers
            // (UserPtConfig) get this for free since the default bound is
            // `usize::MAX + 1`.
            0 < va.end <= C::LOCKED_END_BOUND_spec(),
        ensures
            Self::cursor_new_success_conditions(*va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.invariants_flat(*r.unwrap().1, *final(regions), *final(guards))
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.level == r.unwrap().0.guard_level
                &&& 1 <= r.unwrap().0.guard_level <= NR_LEVELS
                &&& r.unwrap().0.va < r.unwrap().0.barrier_va.end
                &&& r.unwrap().0.va == va.start
                &&& r.unwrap().0.barrier_va == *va
                &&& r.unwrap().1@.as_page_table_owner() == *old(pt_own)
                &&& r.unwrap().0.guard_level == NR_LEVELS ==>
                    r.unwrap().1@.continuations[3].path == old(pt_own).node(old(pt_own).root).path
            },
            !Self::cursor_new_success_conditions(*va) ==> r is Err,
            forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                old(regions).ref_count(idx) != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[idx].paths_in_pt
                        == old(regions).slot_owners[idx].paths_in_pt,
            forall|idx: int| #![trigger final(regions).slot_owners[idx]]
                old(regions).contains(idx)
                && old(regions).ref_count(idx) != REF_COUNT_UNUSED
                ==> final(regions).ref_count(idx) == old(regions).ref_count(idx)
                    && final(regions).slot_owners[idx].usage
                        == old(regions).slot_owners[idx].usage,
            forall|idx: int| #![trigger final(regions).slot_owners[idx].ref_count()]
                final(regions).ref_count(idx) >= REF_COUNT_MAX
                ==> old(regions).ref_count(idx)
                        == final(regions).ref_count(idx),
            forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
                old(regions).ref_count(idx)
                    >= REF_COUNT_MAX
                ==> final(regions).ref_count(idx)
                        == old(regions).ref_count(idx),
            forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
                CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
                CursorMut::<C, A>::item_not_mapped(item, *final(regions)),
            // Non-saturation preservation.
            (forall |i: int| #![trigger old(regions).slot_owners[i]]
                old(regions).contains(i)
                && old(regions).ref_count(i)
                    != REF_COUNT_UNUSED
                ==> old(regions).ref_count(i) + 1
                    < REF_COUNT_MAX)
            ==>
            (forall |i: int| #![trigger final(regions).slot_owners[i]]
                final(regions).contains(i)
                && final(regions).ref_count(i)
                    != REF_COUNT_UNUSED
                ==> final(regions).ref_count(i) + 1 < REF_COUNT_MAX),
    )]
    pub fn new<'owner: 'rcu>(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>) -> Result<
        (Self, Tracked<FlatCursorOwner<'owner, 'rcu, C>>),
        PageTableError,
    > {
        proof {
            C::lemma_paging_consts_properties();
        }

        let valid = is_valid_range::<C>(va);
        if !valid || va.start >= va.end {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        // const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };

        Ok(
            #[verus_spec(with Tracked(pt_own), Ghost(root_guard), Tracked(regions), Tracked(guards))]
            locking::lock_range(pt, guard, va),
        )
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.va,
    {
        self.va
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants])
    /// must hold before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call
    /// - **Correctness**: if the cursor is within the locked range, the result will be `Ok`;
    /// otherwise it will be an error.
    /// - **Correctness**: if there is a mapping present ([Self::query_some_condition]),
    /// then the second field of the result will `Some(item)`, where `item` is the mapping,
    /// and the first field will give its range.
    /// - **Correctness**: if there is no mapping present, then the second field of the result will be
    /// 'None'.
    /// - **Safety**: all frames' relations with the metadata region are preserved.
    /// ## Safety
    /// - The global invariants ensure that the first node we pass through is already locked,
    /// and the loop invariant makes the same guarantee for subsequent nodes.
    /// - This function does not change anything in the metadata region except for incrementing
    /// the reference counts of nodes when it descends into them.
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).invariants_flat(cursor_owner, *old(regions), *old(guards)),
            old(self).query_flat_panic_condition(cursor_owner, *old(regions)) ==> may_panic(),
        ensures
            final(self).invariants_flat(final_owner@, *final(regions), *final(guards)),
            !old(self).query_flat_panic_condition(cursor_owner, *old(regions)),
            cursor_owner.in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                final(self).query_flat_some_condition(final_owner@) ==>
                final(self).query_flat_some_ensures(final_owner@, state),
            res matches Ok(state) ==>
                !final(self).query_flat_some_condition(final_owner@) ==>
                final(self).query_flat_none_ensures(final_owner@, state),
            cursor_owner@.mappings == final_owner@@.mappings,
            final(self).va == old(self).va,
    )]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    pub fn query<'owner: 'rcu>(&mut self) -> Result<PagesState<C>, PageTableError> {
        let ghost initial_owner = cursor_owner;
        let tracked mut owner = cursor_owner;
        if self.va >= self.barrier_va.end {
            return #[verus_spec(with |= Tracked(owner))]
            Err(PageTableError::InvalidVaddr(self.va));
        }
        let rcu_guard = self.rcu_guard;
        #[verus_spec(
            invariant
                self.invariants_flat(owner, *regions, *guards),
                self.va == old(self).va,
                self.va < self.barrier_va.end,
                self.barrier_va == old(self).barrier_va,
                initial_owner@.mappings == owner@.mappings,
                initial_owner@.cur_va == owner@.cur_va,
                old(self).query_flat_panic_condition(initial_owner, *old(regions)) ==> may_panic(),
            decreases self.level,
        )]
        loop {
            proof {
                C::lemma_paging_consts_properties();
                owner.lemma_current_entry_inv(*regions);
            }
            let cur_va = self.va;
            let level = self.level;
            let tracked child_permission = if owner.current_entry().is_node() {
                let ghost child = owner.current_entry().child_paddr();
                let tracked (next_owner, permission) = owner.tracked_lease_child_with_permission(child);
                owner = next_owner;
                Some(permission)
            } else { None };
            let entry = {
                let tracked record = owner.tracked_borrow_current_record();
                #[verus_spec(with
                    Tracked(&record.node), Ghost(owner.current_entry_decode_model()), Tracked(&*regions)
                )]
                self.cur_entry()
            };
            let cur_child = {
                let tracked permission = match child_permission {
                    Some(permission) => permission,
                    None => *entry.node.inner.tracked_metadata_perm.borrow(),
                };
                let tracked record = owner.tracked_borrow_current_record();
                #[verus_spec(with
                    Ghost(owner.current_entry_decode_model()), Tracked(&record.node),
                    Tracked(regions), Tracked(permission)
                )]
                entry.to_ref()
            };
            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    let ghost child = owner.current_entry().child_paddr();
                    // SAFETY: The child is covered by the cursor's range lock.
                    let guard = unsafe {
                        let tracked record = owner.resources.tracked_borrow_record(child);
                        #[verus_spec(with Tracked(&record.node), Tracked(guards))]
                        pt.make_guard_unchecked(rcu_guard)
                    };
                    proof {
                        let ghost path = owner.current_entry().path;
                        let ghost child_level = (owner.level - 1) as PagingLevel;
                        let ghost idx = pte_index_spec::<C>(owner.va, child_level);
                        owner = owner.tracked_push_leased_child(child, idx, path, child_level, guard);
                    }
                    self.push_level(guard);
                    continue;
                },
                ChildRef::None => None,
                ChildRef::Frame(pa, ch_level, prop) => {
                    let ghost idx = owner.current().idx as int;
                    let tracked flat_entry = owner.tracked_borrow_current_record_mut().tracked_take_entry(idx);
                    let tracked mut entry_owner = flat_entry.tracked_into_leaf();
                    let tracked raw_permission = entry_owner.tracked_take_frame_permission();
                    // SAFETY: This is the mapped item's original raw representation.
                    // Clone the item, then restore its permission to the same flat slot.
                    let item = unsafe { C::item_from_raw(pa, level, prop, Tracked(raw_permission)) };
                    #[verus_spec(with Tracked(regions), Ghost(pa))]
                    let cloned = Self::clone_item(&item);
                    let (_pa, _level, _prop, Tracked(restored_permission)) = C::item_into_raw(item);
                    proof {
                        entry_owner.tracked_put_frame_permission(restored_permission);
                        let tracked flat_entry = FlatEntryOwner::tracked_from_leaf(entry_owner);
                        owner.tracked_borrow_current_record_mut().tracked_set_entry(idx, flat_entry);
                    }
                    Some(cloned)
                },
            };
            let size = page_size::<C>(level);
            #[verus_spec(with Tracked(&owner))]
            let range = self.cur_va_range_flat();
            return #[verus_spec(with |= Tracked(owner))]
            Ok((range, item));
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes looking for a mapped (non-absent) leaf entry. If one is found,
    /// returns `Some(va)` where `va` is that entry's address and the cursor
    /// stops there. Otherwise returns `None` and the cursor advances past
    /// the search window.
    ///
    /// This is equivalent to [`find_next_impl`](Self::find_next_impl) with
    /// `find_unmap_subtree = false` and `split_huge = false`: the cursor only
    /// stops at leaf (frame) entries and never splits huge pages.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([Self::find_next_panic_condition]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if a frame is found, the returned address equals the cursor's
    ///   current position, the owner is within the locked range, and the cursor level
    ///   is below the guard level.
    /// - **Correctness**: the found entry is always a frame (never a node or absent).
    ///   If the old entry at the same VA was also a frame, its `prop` field is preserved.
    /// - **Correctness**: if no entry is found, the cursor advances at least `len` bytes
    ///   past its starting position.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).invariants_flat(owner, *old(regions), *old(guards)),
            // Delegates to `find_next_impl`, which diverges on the find-next
            // panic condition.
            old(self).find_next_panic_condition(len) ==> may_panic(),
        ensures
            !old(self).find_next_panic_condition(len),
            final(self).invariants_flat(final_owner@, *final(regions), *final(guards)),
            res is Some ==> {
                &&& res->0 == final(self).va
                &&& final_owner@.level <= final_owner@.guard_level
                &&& final_owner@.in_locked_range()
            },
            res is Some ==> Self::find_not_unmap_subtree_flat_ensures(owner, final_owner@),
            res is None ==> {
                &&& final(self).va >= old(self).va + len
            },
    )]
    pub fn find_next<'owner: 'rcu>(&mut self, len: usize) -> Option<Vaddr> {
        proof_decl! {
            let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>;
        }
        #[verus_spec(with
            Tracked(owner), Tracked(regions), Tracked(guards) => Tracked(next_owner)
        )]
        let result = self.find_next_impl(len, false, false);
        #[verus_spec(with |= Tracked(next_owner))]
        result
    }

    pub open spec fn find_not_unmap_subtree_ensures(
        old_owner: CursorOwner<C>,
        new_owner: CursorOwner<C>,
    ) -> bool {
        let old_cur_entry = old_owner.cur_entry_owner();
        let new_cur_entry = new_owner.cur_entry_owner();
        {
            &&& new_cur_entry.is_frame()
            &&& old_cur_entry.is_frame() ==> new_cur_entry.frame().prop
                == old_cur_entry.frame().prop
        }
    }

    pub open spec fn find_not_unmap_subtree_flat_ensures(
        old_owner: FlatCursorOwner<C>,
        new_owner: FlatCursorOwner<C>,
    ) -> bool {
        &&& new_owner.current_entry().is_frame()
        &&& old_owner.current_entry().is_frame() ==>
            new_owner.current_entry().frame().prop == old_owner.current_entry().frame().prop
    }

    /// Moves the cursor forward to the next fragment in the range.
    ///
    /// See [`Self::find_next`] for more details. Other than the semantics
    /// provided by [`Self::find_next`], this method also supports finding non-
    /// leaf entries and splitting huge pages if necessary.
    ///
    /// `find_unmap_subtree` specifies whether the cursor should stop at the
    /// highest possible level for unmapping. If `false`, the cursor will only
    /// stop at leaf entries.
    ///
    /// `split_huge` specifies whether the cursor should split huge pages when
    /// it finds a huge page that is mapped over the required range (`len`).
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    /// the remaining locked range ([Self::find_next_panic_condition]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Safety**: the cursor's VA never decreases.
    /// - **Correctness**: the returned address reflects the cursor's position after the call.
    /// - **Correctness**: if the result is `Some`, then the current entry is not absent.
    /// - **Correctness**: the `split_huge` flag ensures that the current entry fits the remaining
    /// range, and the cursor position is aligned to `page_size(level)`.
    /// - **Correctness**: if the `split_huge` flag was used, the mappings in the page table
    /// are updated by splitting the next frame to the appropriate size.
    /// - **Correctness**: if the `find_unmap_subtree` flag is false, the found entry is a frame
    /// - **Correctness**: if the `find_unmap_subtree` flag is false, the found frame has the same
    /// `prop` field as the previous frame in that va (even if it is the result of a split).
    /// - **Correctness**: mappings in the page table are preserved except for the possible split.
    /// - **Correctness**: if no entry is found, the cursor advances at least `len` bytes past its starting position.
    /// - **Correctness**: no mappings exist prior to the found entry within the search range. If no
    /// entry is found, then no mappings exist in the search range at all.
    /// - **Liveness**: The cursor is within the locked range, at a safe level, and properly aligned,
    /// ready to map or protect a new frame.
    /// ## Safety
    /// - This function never accesses nodes outside the locked range, because it is impossible to
    /// create a cursor below the range, and if the cursor is above the range this function will always panic.
    #[verifier::rlimit(200)]
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                 -> final_cursor_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).invariants_flat(cursor_owner, *old(regions), *old(guards)),
            // The runtime `assert!`s diverge unless `len` is page-aligned and
            // the scan stays within the cursor's barrier.
            old(self).find_next_panic_condition(len) ==> may_panic(),
        ensures
            !old(self).find_next_panic_condition(len),
            final(self).invariants_flat(final_cursor_owner@, *final(regions), *final(guards)),
            final(self).barrier_va == old(self).barrier_va,
            final(self).guard_level == old(self).guard_level,
            final(self).va >= old(self).va,
            res is Some ==> {
                &&& res->0 == final(self).va
                &&& final_cursor_owner@.level <= final_cursor_owner@.guard_level
                &&& final_cursor_owner@.in_locked_range()
                &&& final(self).va < old(self).va + len
            },
            res is Some ==> !final_cursor_owner@.cur_entry_owner().is_absent(),
            res is Some && split_huge ==> {
                &&& final_cursor_owner@@.mappings == cursor_owner@.split_while_huge(page_size::<PagingConsts>(final(self).level)).mappings
                &&& final(self).va + page_size::<PagingConsts>(final(self).level) <= old(self).va + len
                &&& nat_align_down(final(self).va as nat, page_size::<PagingConsts>(final(self).level) as nat) as usize == final(self).va
            },
            res is Some && !find_unmap_subtree ==> Self::find_not_unmap_subtree_flat_ensures(cursor_owner, final_cursor_owner@),
            res is Some && final_cursor_owner@.cur_entry_owner().is_node() ==>
                final_cursor_owner@@.mappings == cursor_owner@.mappings,
            res is Some && find_unmap_subtree && final_cursor_owner@.cur_entry_owner().is_node()
                ==> C::TOP_LEVEL_CAN_UNMAP_spec() || final(self).level < NR_LEVELS,
            cursor_owner@.mappings.filter(|m: Mapping|
                old(self).va <= m.va_range.start < final(self).va) == Set::<Mapping>::empty(),
            res is None ==> {
                &&& final(self).va >= old(self).va + len
                &&& final_cursor_owner@@.mappings == cursor_owner@.mappings
            },
            res is Some && final(self).va > old(self).va ==> !cursor_owner@.present(),
    )]
    #[verifier::spinoff_prover]
    fn find_next_impl<'owner: 'rcu>(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> Option<
        Vaddr,
    > {
        assert_eq!(len % PAGE_SIZE, 0);

        // [KNOWN] BUG FOUND BY FV: `self.va + len` could overflow. For now assume that it doesn't. https://github.com/asterinas/asterinas/issues/3159
        assume(self.va + len <= usize::MAX);
        let end = self.va + len;
        assert!(end <= self.barrier_va.end);

        let rcu_guard = self.rcu_guard;
        let ghost initial_owner = cursor_owner;
        let tracked mut owner = cursor_owner;
        let ghost mut split_happened = false;

        #[verus_spec(
            invariant
                self.invariants_flat(owner, *regions, *guards),
                initial_owner.inv(),
                self.barrier_va == old(self).barrier_va,
                self.guard_level == old(self).guard_level,
                old(self).va <= self.va,
                end == old(self).va + len,
                end % PAGE_SIZE == 0,
                end <= self.barrier_va.end,
                owner.in_locked_range() || self.va >= end,
                !split_happened ==> owner@.mappings == initial_owner@.mappings,
                initial_owner@.mappings.filter(
                    |m: Mapping| old(self).va <= m.va_range.start < self.va,
                ) == Set::<Mapping>::empty(),
                split_happened ==> owner.current_entry().is_frame(),
                split_happened ==> self.va < end,
                split_happened ==> self.va == old(self).va,
                split_happened ==> owner@.mappings == initial_owner@.split_while_huge(
                    page_size::<PagingConsts>(self.level),
                ).mappings,
                initial_owner.current_entry().is_frame() ==> {
                    &&& owner.current_entry().is_frame()
                    &&& owner.current_entry().frame().prop == initial_owner.current_entry().frame().prop
                },
                self.va > old(self).va ==> !initial_owner@.present(),
            decreases end - self.va, self.level,
        )]
        while self.va < end {
            proof {
                C::lemma_paging_consts_properties();
                owner.lemma_current_entry_inv(*regions);
            }
            let cur_va = self.va;
            #[verus_spec(with Tracked(&owner))]
            let cur_va_range = self.cur_va_range_flat();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            // This reference comes from the authoritative permission slot, not
            // from a recursively extracted child that must later be restored.
            let tracked child_permission = if owner.current_entry().is_node() {
                let ghost child = owner.current_entry().child_paddr();
                let tracked (next_owner, permission) =
                    owner.tracked_lease_child_with_permission(child);
                owner = next_owner;
                Some(permission)
            } else {
                None
            };
            let mut cur_entry = {
                let tracked record = owner.tracked_borrow_current_record();
                #[verus_spec(with
                    Tracked(&record.node), Ghost(owner.current_entry_decode_model()),
                    Tracked(&*regions)
                )]
                self.cur_entry()
            };
            let cur_child = {
                let tracked metadata_permission = match child_permission {
                    Some(permission) => permission,
                    None => *cur_entry.node.inner.tracked_metadata_perm.borrow(),
                };
                let tracked record = owner.tracked_borrow_current_record();
                #[verus_spec(with
                    Ghost(owner.current_entry_decode_model()), Tracked(&record.node),
                    Tracked(regions), Tracked(metadata_permission)
                )]
                cur_entry.to_ref()
            };

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range
                        && (C::TOP_LEVEL_CAN_UNMAP() || self.level != C::NR_LEVELS()) {
                        return #[verus_spec(with |= Tracked(owner))]
                        Some(cur_va);
                    }
                    let ghost child = owner.current_entry().child_paddr();
                    // SAFETY: The range lock covers this child; no guard for it exists.
                    let mut pt_guard = unsafe {
                        let tracked record = owner.resources.tracked_borrow_record(child);
                        #[verus_spec(with Tracked(&record.node), Tracked(guards))]
                        pt.make_guard_unchecked(rcu_guard)
                    };
                    let nr_children = {
                        let tracked record = owner.resources.tracked_borrow_record(child);
                        #[verus_spec(with Tracked(&record.node))]
                        pt_guard.nr_children()
                    };
                    if nr_children != 0 {
                        proof {
                            let ghost path = owner.current_entry().path;
                            let ghost child_level = (owner.level - 1) as PagingLevel;
                            let ghost idx = pte_index_spec::<C>(owner.va, child_level);
                            owner = owner.tracked_push_leased_child(
                                child, idx, path, child_level, pt_guard,
                            );
                        }
                        self.push_level(pt_guard);
                    } else {
                        proof_decl! {
                            let tracked guard_obl = pt_guard.tracked_redeem(guards);
                        }
                        proof_with!(Tracked(guard_obl));
                        let _ = vstd_extra::drop_tracking::ManuallyDrop::new(pt_guard);
                        #[verus_spec(with Tracked(&mut owner), Tracked(&*regions), Tracked(guards))]
                        self.move_forward_flat();
                    }
                    continue;
                },
                ChildRef::None => {
                    #[verus_spec(with Tracked(&mut owner), Tracked(&*regions), Tracked(guards))]
                    self.move_forward_flat();
                    continue;
                },
                ChildRef::Frame(_, _, _) => {
                    if cur_entry_fits_range || !split_huge {
                        return #[verus_spec(with |= Tracked(owner))]
                        Some(cur_va);
                    }
                    /* Bind the hidden owner return before unwrapping the Option.
                     * Origin Rust:
                     * let split_child = cur_entry.split_if_mapped_huge(rcu_guard)
                     *     .expect("The entry must be a huge page");
                     */
                    proof_decl! {
                        let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>;
                    }
                    #[verus_spec(with
                        Tracked(owner), Tracked(regions), Tracked(guards) => Tracked(next_owner)
                    )]
                    let split_child = cur_entry.split_if_mapped_huge(rcu_guard);
                    let split_child = split_child.expect("The entry must be a huge page");
                    proof {
                        let ghost child = next_owner.current_entry().child_paddr();
                        let ghost path = next_owner.current_entry().path;
                        let ghost child_level = (next_owner.level - 1) as PagingLevel;
                        let ghost idx = pte_index_spec::<C>(next_owner.va, child_level);
                        owner = next_owner.tracked_push_leased_child(
                            child, idx, path, child_level, split_child,
                        );
                        split_happened = true;
                    }
                    self.push_level(split_child);
                    continue;
                },
            }
        }
        #[verus_spec(with |= Tracked(owner))]
        None
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants]) must hold.
    /// - **Safety**: the function will panic if `va` is not page aligned ([Self::jump_panic_condition]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if `va` is within the barrier range, the result is `Ok` and the
    ///   cursor's VA is set to exactly `va`.
    /// - **Correctness**: if `va` is outside the barrier range, the result is `Err`.
    /// ## Safety
    /// - The mappings in the page table are unchanged; `jump` only repositions the cursor
    ///   by ascending to a common ancestor and updating the slot index within a node.
    /// - On a successful jump the cursor is guaranteed to be within the locked range, so
    ///   it will be safe to use.
    #[verifier::rlimit(200)]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(self).jump_panic_condition(va) ==> may_panic(),
        ensures
            !old(self).jump_panic_condition(va),
            final(self).invariants(*final(owner), *final(regions), *final(guards)),
            final(self).barrier_va.start <= va < final(self).barrier_va.end ==> {
                &&& res is Ok
                &&& final(self).va == va
            },
            !(final(self).barrier_va.start <= va < final(self).barrier_va.end) ==> res is Err,
    )]
    #[verifier::spinoff_prover]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
        assert_eq!(va % PAGE_SIZE, 0);

        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        #[verus_spec(
            invariant
                owner.inv(),
                self.inv(),
                self.wf(*owner),
                regions.inv(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.metaregion_sound(*regions),
                self.barrier_va.start <= va < self.barrier_va.end,
                va % PAGE_SIZE == 0,
                old(self).jump_panic_condition(va) ==> may_panic(),
                self.va == old(self).va,
                self.barrier_va == old(self).barrier_va,
                self.guard_level == old(self).guard_level,
                old(self).level <= self.level,
                // Structural accumulator: every guard-level node already
                // popped past failed to contain `va`.
                forall|k: PagingLevel|
                    #![trigger old(self).jump_node_holds(k, va)]
                    old(self).level <= k < self.level && k <= self.guard_level ==> !old(
                        self,
                    ).jump_node_holds(k, va),
            decreases NR_LEVELS - self.level,
        )]
        loop {
            proof {
                C::lemma_paging_consts_properties();
            }
            let node_size = page_size::<C>(self.level + 1);
            let node_start = self.va.align_down(node_size);

            if self.level <= self.guard_level && node_start <= va && va - node_start < node_size {
                proof {
                    assert(old(self).jump_node_holds(self.level, va));
                }
                let ghost owner0 = *owner;
                let ghost old_va = self.va;
                self.va = va;
                proof {
                    C::lemma_paging_consts_properties();
                    // At level == NR_LEVELS the quantifier in set_va_in_node is vacuous.
                    if self.level < NR_LEVELS as PagingLevel {
                        lemma_same_node_pte_indices_match::<C>(va, old_va, node_start, self.level);
                    }
                    lemma_same_node_vaddr_upper_bits_match::<C>(va, old_va, node_start, self.level);

                    owner.tracked_set_vaddr_in_node(va);
                    assert(owner.children_not_locked(*guards) && owner.metaregion_sound(*regions))
                        by {
                        reveal(CursorContinuation::map_children);
                        reveal(CursorOwner::path_metaregion_sound);
                    };
                }

                return Ok(());
            }
            proof {
                if self.level <= self.guard_level && self.level >= NR_LEVELS as PagingLevel {
                    owner.lemma_in_node_holds_at_top(self.va, va, node_size);
                }
            }
            let ghost guards_before_pop = *guards;
            let ghost popped_guard = self.path[self.level - 1]->0;
            #[verus_spec(with Tracked(guards))]
            self.pop_level();
            proof {
                owner.pop_level_owner_preserves_invs(guards_before_pop, *regions);
                let ghost owner_before_pop = *owner;
                let ghost old_level = owner.level;
                let tracked mut parent = owner.continuations.tracked_remove(old_level as int);
                let tracked child = owner.continuations.tracked_remove(old_level - 1);
                parent.tracked_restore(child);
                let ghost restored_parent = parent;
                owner.continuations.tracked_insert(old_level as int, parent);
                owner.level = (old_level + 1) as u8;
                owner.popped_too_high = owner.level >= owner.guard_level;
                assert(owner.continuations =~= owner_before_pop.continuations.insert(
                    old_level as int, restored_parent,
                ).remove(old_level - 1));
                assert(*owner == owner_before_pop.pop_level_owner().0);
            }
            proof {
                owner.lemma_never_drop_restores_children_not_locked(
                    popped_guard, guards_before_pop, *guards,
                );
            }
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    ///
    /// Advances the cursor past the current slot. If the current slot is the
    /// last entry in its page-table node, the cursor pops up one or more
    /// levels (via [`Self::pop_level`]) until it reaches a node with a
    /// subsequent entry, then positions itself at that entry.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the object invariants for the cursor and metadata regions
    ///   must hold.
    /// - **Correctness**: the cursor must be within the locked range before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: all safety invariants are preserved.
    /// - **Correctness**: cursor advances forward a slot, and pops levels if necessary.
    /// ## Safety
    /// - This function is safe because it only manipulates the cursor, it does not modify
    ///   any of the entries. It can advance the cursor outside of the locked range, however.
    #[verifier::rlimit(200)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).inv(),
            old(regions).inv(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).metaregion_sound(*old(regions)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
        ensures
            final(owner).inv(),
            final(self).wf(*final(owner)),
            final(self).inv(),
            final(regions).inv(),
            *final(owner) == old(owner).move_forward_owner_spec(),
            final(owner).max_steps() < old(owner).max_steps(),
            final(self).barrier_va == old(self).barrier_va,
            final(self).guard_level == old(self).guard_level,
            !final(owner).popped_too_high,
            final(owner).in_locked_range() || final(owner).above_locked_range(),
            final(owner).children_not_locked(*final(guards)),
            final(owner).nodes_locked(*final(guards)),
            final(owner).metaregion_sound(*final(regions)),
            final(owner).va == old(owner)@.align_up_spec(page_size::<PagingConsts>(old(self).level)),
            final(self).va <= old(self).va + page_size::<PagingConsts>(old(self).level),
            // Slots and slot_owners fully unchanged (pop_level is purely cursor manipulation).
            final(regions).slots == old(regions).slots,
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx]]
                final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
    )]
    #[verifier::spinoff_prover]
    fn move_forward(&mut self) {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        proof {
            owner.lemma_in_locked_range_guard_index_eq_prefix();
            owner.move_forward_owner_decreases_steps();
            old(owner).move_forward_not_popped_too_high();
        }

        let ghost start_level = self.level;
        let ghost guard_level = self.guard_level;
        let ghost barrier_va = self.barrier_va;
        let ghost va = self.va;

        let next_va = (#[verus_spec(with Tracked(owner))]
        self.cur_va_range()).end;

        proof {
            C::lemma_paging_consts_properties();
            owner0.lemma_va_plus_page_size_no_overflow(start_level);
            lemma_page_size_ge_base::<PagingConsts>(start_level);
            vstd_extra::arithmetic::lemma_nat_align_down_sound(
                va as nat,
                page_size::<PagingConsts>(start_level) as nat,
            );
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(
                nat_align_down(va as nat, page_size::<PagingConsts>(start_level) as nat) as int,
                page_size::<PagingConsts>(start_level) as int,
            );
        }

        #[verus_spec(
            invariant
                owner.inv(),
                self.wf(*owner),
                self.inv(),
                regions.inv(),
                self.guard_level == guard_level,
                self.barrier_va == barrier_va,
                owner.move_forward_owner_spec() == owner0.move_forward_owner_spec(),
                1 <= start_level <= self.level <= self.guard_level <= NR_LEVELS,
                C::NR_LEVELS() == NR_LEVELS,
                owner.va == va,
                owner0.va == va,
                va < next_va <= va + page_size::<C>(self.level),
                next_va % page_size::<C>(self.level) == 0,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.metaregion_sound(*regions),
                *regions == regions0,
            decreases self.guard_level - self.level,
        )]
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0 {
            proof {
                C::lemma_paging_consts_properties();
                lemma_next_slot_pte_index::<C>(va, next_va, self.level);
                lemma_page_size_next::<C>(self.level);
                owner.lemma_cur_pte_index();
                assert(owner.index() + 1 == NR_ENTRIES);
                assert(owner.move_forward_owner_spec()
                    == owner.pop_level_owner().0.move_forward_owner_spec());
            }

            let ghost guards_before_pop = *guards;
            let ghost popped_guard = self.path[self.level - 1]->0;
            #[verus_spec(with Tracked(guards))]
            self.pop_level();
            proof {
                owner.pop_level_owner_preserves_invs(guards_before_pop, *regions);
                let ghost owner_before_pop = *owner;
                let ghost old_level = owner.level;
                let tracked mut parent = owner.continuations.tracked_remove(old_level as int);
                let tracked child = owner.continuations.tracked_remove(old_level - 1);
                parent.tracked_restore(child);
                let ghost restored_parent = parent;
                owner.continuations.tracked_insert(old_level as int, parent);
                owner.level = (old_level + 1) as u8;
                owner.popped_too_high = owner.level >= owner.guard_level;
                assert(owner.continuations =~= owner_before_pop.continuations.insert(
                    old_level as int, restored_parent,
                ).remove(old_level - 1));
                assert(*owner == owner_before_pop.pop_level_owner().0);
            }
            proof {
                owner.lemma_never_drop_restores_children_not_locked(
                    popped_guard, guards_before_pop, *guards,
                );
            }
        }

        proof {
            C::lemma_paging_consts_properties();
            lemma_next_slot_pte_index::<C>(va, next_va, self.level);
            owner.lemma_cur_pte_index();
            if pte_index_spec::<C>(next_va, (self.level - 1 + 1) as PagingLevel) == 0 {
                assert(self.level == self.guard_level);
                owner.lemma_in_locked_range_guard_index_eq_prefix();
                lemma_pte_index_bound::<C>(owner.va, owner.level);
                assert(owner.index() + 1 < NR_ENTRIES);
            }
            assert(owner.index() + 1 < NR_ENTRIES);
        }

        self.va = next_va;

        proof {
            if owner.level == NR_LEVELS {
                owner0.lemma_in_locked_range_top_index_lt_top_end();
                lemma_pte_index_bound::<C>(va, NR_LEVELS as PagingLevel);
                assert(pte_index_spec::<C>(owner0.va, (NR_LEVELS - 1 + 1) as PagingLevel)
                    < C::TOP_LEVEL_INDEX_RANGE().end);
                assert(owner.continuations[owner.level - 1].idx + 1
                    <= C::TOP_LEVEL_INDEX_RANGE().end);
            }
            owner.do_inc_index();
            owner.zero_preserves_all_but_va();
            owner.do_zero_below_level();
            owner0.move_forward_va_is_align_up();
            assert(owner.children_not_locked(*guards) && owner.metaregion_sound(*regions)) by {
                reveal(CursorContinuation::map_children);
                reveal(CursorOwner::path_metaregion_sound);
            };
            if owner.level < owner.guard_level {
                owner.lemma_prefix_in_locked_range();
            }
        }
    }

    // Flat navigation uses the same runtime steps as move_forward. The legacy
    // entry point remains until map/take callers no longer own recursive trees.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut FlatCursorOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            old(self).invariants_flat(*old(owner), *regions, *old(guards)),
            old(owner).in_locked_range(),
        ensures
            final(self).invariants_flat(*final(owner), *regions, *final(guards)),
            final(owner).resources == old(owner).resources,
            final(owner).as_page_table_owner() == old(owner).as_page_table_owner(),
            final(self).barrier_va == old(self).barrier_va,
            final(self).guard_level == old(self).guard_level,
            old(self).va < final(self).va,
            final(self).va == old(owner).cur_va_range().end,
            final(self).va <= old(self).va + page_size::<C>(old(self).level),
            final(owner).in_locked_range() || final(owner).above_locked_range(),
    )]
    fn move_forward_flat(&mut self) {
        proof {
            C::lemma_paging_consts_properties();
        }
        let ghost initial_owner = *owner;
        let ghost initial_va = self.va;
        let ghost initial_level = self.level;
        let next_va = (#[verus_spec(with Tracked(&*owner))]
        self.cur_va_range_flat()).end;

        #[verus_spec(
            invariant
                self.invariants_flat(*owner, *regions, *guards),
                C::NR_LEVELS() == NR_LEVELS,
                owner.resources == initial_owner.resources,
                owner.va == initial_va,
                initial_level <= self.level <= self.guard_level,
                self.guard_level == old(self).guard_level,
                self.barrier_va == old(self).barrier_va,
                next_va == initial_owner.cur_va_range().end,
            decreases self.guard_level - self.level,
        )]
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0 {
            #[verus_spec(with Tracked(guards))]
            self.pop_level();
            proof {
                owner.tracked_pop_level();
            }
        }
        self.va = next_va;
        proof {
            owner.tracked_set_va_in_node(next_va);
        }
    }

    #[verus_spec(res =>
        with Tracked(owner): Tracked<&FlatCursorOwner<C>>,
        requires
            owner.inv(),
            self.wf_flat(*owner),
            owner.in_locked_range(),
            1 <= self.level <= owner.guard_level,
        ensures
            res.start <= self.va,
            res.end <= self.va + page_size::<C>(self.level),
            res.start == self.va ==> res.end == self.va + page_size::<C>(self.level),
        returns owner.cur_va_range(),
    )]
    fn cur_va_range_flat(&self) -> Range<Vaddr> {
        proof {
            C::lemma_paging_consts_properties();
            owner.lemma_cur_va_range_bounds();
        }
        let page_size = page_size::<C>(self.level);
        let start = self.va.align_down(page_size);
        start..start + page_size
    }

    /// Ascends one level by removing the current guard and releasing its
    /// proof-side lock obligation. The caller updates owner navigation.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the cursor is valid and its current guard is lock-held.
    /// - The cursor must be below the guard level (`level < guard_level`).
    /// ## Postconditions
    /// - **Safety Invariants**: all safety invariants are preserved; the metadata region is
    ///   completely unchanged.
    /// - **Correctness**: only the current path slot and cursor level change.
    /// ## Safety
    /// - It is safe to pop the cursor as long as it is not already at the top level,
    ///   but if it pops above the guard level, it is not safe to access the page table.
    ///   This is represented by the "popped too high" flag which must be cleared by the caller.
    #[verus_spec(
        with Tracked(guards): Tracked<&mut Guards>,
        requires
            old(self).inv(),
            old(self).level <= NR_LEVELS,
            old(self).level > old(self).guard_level ==> may_panic(),
            old(self).level <= old(self).guard_level ==>
                old(self).path[old(self).level - 1] is Some,
            old(self).level > old(self).guard_level ==>
                old(self).path[old(self).level - 1] is None,
            old(self).path[old(self).level - 1] matches Some(guard) ==>
                old(guards).lock_held(guard.inner.inner@.ptr.addr()),
        ensures
            old(self).level <= old(self).guard_level,
            final(self).inv(),
            final(self).level == old(self).level + 1,
            final(self).guard_level == old(self).guard_level,
            final(self).barrier_va == old(self).barrier_va,
            final(self).va == old(self).va,
            final(self).rcu_guard == old(self).rcu_guard,
            final(self).path[old(self).level - 1] is None,
            forall|i: int| 0 <= i < NR_LEVELS && i != old(self).level - 1 ==>
                #[trigger] final(self).path[i] == old(self).path[i],
            final(guards).guards == old(guards).guards.remove(
                old(self).path[old(self).level - 1]->0.inner.inner@.ptr.addr(),
            ),
    )]
    #[verifier::spinoff_prover]
    fn pop_level(&mut self) {
        let taken = self.path[self.level as usize - 1].take().unwrap_or_panic();
        proof_decl! {
            let tracked guard_obl = taken.tracked_redeem(guards);
        }
        proof_with!(Tracked(guard_obl));
        let md = vstd_extra::drop_tracking::ManuallyDrop::new(taken);
        self.level = self.level + 1;
    }

    /// Descends one level by retaining an already-created child guard.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the cursor is valid and can descend one level.
    /// ## Postconditions
    /// - **Safety Invariants**: all safety invariants are preserved.
    /// - **Correctness**: `self.level` decreases by 1, `self.va` is unchanged,
    ///   and abstract mappings are preserved.
    /// - **Correctness**: only the new path slot and cursor level change.
    /// ## Safety
    /// - The caller creates the guard and updates the corresponding owner navigation.
    /// - It otherwise does not change the page table or metadata regions.
    #[verus_spec(
        requires
            old(self).inv(),
            1 < old(self).level <= old(self).guard_level,
        ensures
            final(self).inv(),
            final(self).level == old(self).level - 1,
            final(self).guard_level == old(self).guard_level,
            final(self).barrier_va == old(self).barrier_va,
            final(self).va == old(self).va,
            final(self).rcu_guard == old(self).rcu_guard,
            final(self).path[old(self).level - 2] == Some(child_pt),
            forall|i: int| 0 <= i < NR_LEVELS && i != old(self).level - 2 ==>
                #[trigger] final(self).path[i] == old(self).path[i],
    )]
    #[verifier::spinoff_prover]
    fn push_level(&mut self, child_pt: PageTableGuard<'rcu, C>) {
        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level());

        // let old = self.path[self.level as usize - 1].replace(child_pt);
        self.path[self.level as usize - 1] = Some(child_pt);
        // debug_assert!(old.is_none());
    }

    #[verus_spec(res =>
        with Tracked(parent_owner): Tracked<&NodeOwner<C>>,
             Ghost(entry_model): Ghost<EntryOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            old(self).inv(),
            1 <= old(self).level <= NR_LEVELS,
            old(self).path[old(self).level - 1] is Some,
            parent_owner.inv(),
            parent_owner.relate_guard(old(self).path[old(self).level - 1]->0),
            parent_owner.level() == old(self).level,
            entry_model.inv(),
            entry_model.parent_level == old(self).level,
            entry_model.match_pte(
                parent_owner.children_perm.value()[pte_index_spec::<C>(old(self).va, old(self).level) as int],
                entry_model.parent_level,
            ),
            regions.inv(),
            regions.slots.contains_key(parent_owner.slot_index),
        ensures
            res.wf(entry_model),
            res.pte == parent_owner.children_perm.value()[res.idx as int],
            res.idx == pte_index_spec::<C>(old(self).va, old(self).level),
            final(self).level == old(self).level,
            final(self).guard_level == old(self).guard_level,
            final(self).va == old(self).va,
            final(self).barrier_va == old(self).barrier_va,
            final(self).rcu_guard == old(self).rcu_guard,
            *res.node == old(self).path[old(self).level - 1]->0,
            final(self).path[old(self).level - 1] is Some,
            final(self).path[old(self).level - 1]->0 == *final(res.node),
            forall|i: int|
                0 <= i < NR_LEVELS && i != old(self).level - 1 ==>
                    #[trigger] final(self).path[i] == old(self).path[i],
            parent_owner.relate_guard(*res.node),
    )]
    #[verifier::spinoff_prover]
    fn cur_entry(&mut self) -> Entry<'_, 'rcu, C> {
        proof {
            C::lemma_paging_consts_properties();
            lemma_pte_index_bound::<C>(self.va, self.level);
        }
        let node = path_slot_as_mut(&mut self.path, self.level as usize - 1);
        #[verus_spec(with Tracked(parent_owner), Ghost(entry_model), Tracked(regions))]
        node.entry(pte_index::<C>(self.va, self.level))
    }

    /// Gets the virtual address range that the current entry covers.
    ///
    /// Returns `[align_down(va, page_size(level)) .. align_down(va, page_size(level)) + page_size(level))`,
    /// i.e. the slot at the cursor's current level that contains the cursor's VA.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the cursor owner must be valid (`owner.inv()`) and
    ///   the cursor must be well-formed w.r.t. the owner (`self.wf(*owner)`).
    /// ## Postconditions
    /// - **Correctness**: the returned range corresponds to the abstract `owner.cur_va_range()`.
    /// - **Correctness**: the range contains the cursor's va.
    /// - **Correctness**: when the cursor is at the start of the slot (`res.start == self.va`),
    ///   the range is exactly `[self.va .. self.va + page_size(level))`.
    /// ## Safety
    /// - This function does not modify any relevant structures, so it is perfectly safe.
    #[verus_spec(res =>
        with
            Tracked(owner): Tracked<&CursorOwner<C>>,
        requires
            owner.inv(),
            self.wf(*owner),
            owner.in_locked_range(),
            1 <= self.level <= owner.guard_level,
        ensures
            res.start <= self.va,
            res.end <= self.va + page_size::<PagingConsts>(self.level),
            res.start == self.va ==> res.end == self.va + page_size::<PagingConsts>(self.level),
        returns
            owner.cur_va_range(),
    )]
    fn cur_va_range(&self) -> Range<Vaddr> {
        proof {
            C::lemma_paging_consts_properties();
        }
        let page_size = page_size::<C>(self.level);
        let start = self.va.align_down(page_size);

        proof {
            // Bound the returned range end.
            owner.lemma_va_plus_page_size_no_overflow(self.level);
        }

        start..start + page_size
    }
}

/*
impl<C: PageTableConfig> Drop for Cursor<'_, C> {
    fn drop(&mut self) {
        locking::unlock_range(self);
    }
}
*/

#[verus_verify]
impl<'rcu, C: PageTableConfig, A: InAtomicMode> CursorMut<'rcu, C, A> {
    #[verifier::rlimit(200)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut FlatCursorOwner<'_, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            old(self).0.invariants_flat(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            old(owner).cur_entry_owner().is_frame(),
            forall |p: PageProperty| op.requires((p,)),
            forall |pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty,
                perm: Tracked<Option<C::Perm>>| #![auto]
                op.ensures((p_in,), p_out) ==> (
                    C::item_into_raw(C::item_from_raw(pa, level, p_out, perm)).3@
                        is Some
                ) == (perm@ is Some),
            forall |pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty| #![auto]
                op.ensures((p_in,), p_out) && C::E::new_page_req(pa, level, p_in) ==>
                    C::E::new_page_req(pa, level, p_out),
        ensures
            final(self).0.invariants_flat(*final(owner), *final(regions), *final(guards)),
            final(self).0.barrier_va == old(self).0.barrier_va,
            final(self).0.va == old(self).0.va,
            final(self).0.level == old(self).0.level,
            final(owner).va == old(owner).va,
            final(owner).in_locked_range(),
            !final(owner).popped_too_high,
            *final(regions) == *old(regions),
            *final(guards) == *old(guards),
    )]
    #[verifier::spinoff_prover]
    fn protect_cur_entry(&mut self, op: impl FnOnce(PageProperty) -> PageProperty) {
        let ghost initial_owner = *owner;
        let ghost initial_record = owner.current_record();
        let ghost initial_pt = owner.as_page_table_owner();
        proof {
            C::lemma_paging_consts_properties();
            owner.lemma_current_entry_inv(*regions);
            assert(initial_pt.contains_node(initial_owner.current_paddr()));
            assert(initial_pt.node(initial_owner.current_paddr()) == initial_record);
            reveal(FlatCursorResources::inv);
        }
        let entry_idx = pte_index::<C>(self.0.va, self.0.level);
        let tracked record = owner.tracked_borrow_current_record_mut();
        let node = path_slot_as_mut(&mut self.0.path, self.0.level as usize - 1);
        let tracked entry_owner = record.entries.tracked_borrow_mut(entry_idx as int);
        #[verus_spec(with
            Tracked(entry_owner), Tracked(&mut record.node), Tracked(&*regions)
        )]
        let _pte = node.protect_child(entry_idx, op);
        proof {
            assert(record.local_inv()) by {
                assert forall|i: int| 0 <= i < NR_ENTRIES implies {
                    let entry = #[trigger] record.entries[i];
                    let pte = record.node.children_perm.value()[i];
                    &&& entry.inv()
                    &&& entry.path == record.path.push_tail(i)
                    &&& entry.parent_level == record.node.level
                    &&& entry.match_pte(pte) || (record.node.level == NR_LEVELS
                        && C::LEADING_BITS_spec() == 0 && entry.borrowed_match_pte(pte))
                } by {
                    if i != entry_idx {
                        assert(initial_record.entries[i] == record.entries[i]);
                    }
                };
            };
            assert(record.paddr() == initial_owner.current_paddr());
            if initial_owner.resources.contains_raw_leased(initial_owner.current_paddr()) {
                assert(record.node.permission_matches(
                    *initial_owner.resources.leases[initial_owner.current_paddr()].permission));
            }
            assert(owner.resources.inv());
            assert(owner.current_record().local_inv());
            let updated_pt = owner.as_page_table_owner();
            assert(initial_pt.same_node_edges(updated_pt)) by {
                assert(initial_pt.nodes.dom() == updated_pt.nodes.dom());
                assert forall|paddr: Paddr| #[trigger] initial_pt.contains_node(paddr) implies {
                    &&& initial_pt.node(paddr).entries.len() == NR_ENTRIES
                    &&& updated_pt.node(paddr).entries.len() == NR_ENTRIES
                    &&& initial_pt.node(paddr).path == updated_pt.node(paddr).path
                    &&& initial_pt.node(paddr).node.level == updated_pt.node(paddr).node.level
                    &&& forall|i: int| 0 <= i < NR_ENTRIES ==> {
                        let entry = #[trigger] initial_pt.node(paddr).entries[i];
                        let updated = updated_pt.node(paddr).entries[i];
                        &&& entry.is_node() == updated.is_node()
                        &&& entry.is_node() ==> entry.child_paddr() == updated.child_paddr()
                    }
                } by {
                    initial_pt.lemma_node_inv(paddr);
                };
            };
            assert forall|paddr: Paddr| #[trigger] updated_pt.contains_node(paddr)
                implies updated_pt.local_node_inv(paddr) by {
                initial_pt.lemma_node_inv(paddr);
            };
            initial_pt.lemma_same_edges_inv(updated_pt);
            assert(owner.inv());
        }
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<&'owner mut FlatPageTableOwner<C>>,
             Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            pt.relates_flat_owner(*old(pt_own), *old(regions)),
            old(pt_own).node(old(pt_own).root).node.relate_guard(root_guard),
            // Per-config tightening; see `Cursor::new`.
            0 < va.end <= C::LOCKED_END_BOUND_spec(),
        ensures
            Cursor::<C, A>::cursor_new_success_conditions(*va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.0.invariants_flat(*r.unwrap().1, *final(regions), *final(guards))
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.0.level == r.unwrap().0.0.guard_level
                &&& 1 <= r.unwrap().0.0.guard_level <= NR_LEVELS
                &&& r.unwrap().0.0.va < r.unwrap().0.0.barrier_va.end
                &&& r.unwrap().0.0.va == va.start
                &&& r.unwrap().0.0.barrier_va == *va
            },
            !Cursor::<C, A>::cursor_new_success_conditions(*va) ==> r is Err,
            // cursor_mut only acquires locks on page-table node slots; it does not
            // set paths_in_pt for data-frame slots. Any frame that was item_not_mapped
            // before the call remains item_not_mapped after.
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *final(regions)),
            // CursorMut::new inherits the weakened Cursor::new preservation:
            // PT-node allocations come from UNUSED slots, so any slot that
            // was already in use keeps its paths_in_pt.
            forall |idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                old(regions).ref_count(idx)
                    != REF_COUNT_UNUSED
                ==> final(regions).slot_owners[idx].paths_in_pt
                        == old(regions).slot_owners[idx].paths_in_pt,
            forall|idx: int| #![trigger final(regions).slot_owners[idx]]
                old(regions).contains(idx)
                && old(regions).ref_count(idx)
                    != REF_COUNT_UNUSED
                ==> final(regions).ref_count(idx)
                        == old(regions).ref_count(idx)
                    && final(regions).slot_owners[idx].usage
                        == old(regions).slot_owners[idx].usage,
    )]
    pub fn new<'owner: 'rcu>(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>) -> Result<
        (Self, Tracked<FlatCursorOwner<'owner, 'rcu, C>>),
        PageTableError,
    > {
        let res =
            #[verus_spec(with Tracked(pt_own), Ghost(root_guard), Tracked(regions), Tracked(guards))]
        Cursor::new(pt, guard, va);
        match res {
            Ok((inner_cursor, tracked_owner)) => {
                proof {
                    // In the Ok branch, cursor_new_success_conditions(va) holds
                    // (from !conditions ==> Err, contrapositive gives Ok ==> conditions).
                    // Therefore the success-case ensures apply, giving us invariants.
                }
                Ok((Self(inner_cursor), tracked_owner))
            },
            Err(e) => Err(e),
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes looking for a mapped (non-absent) leaf entry. If one is found,
    /// returns `Some(va)` where `va` is that entry's address and the cursor
    /// stops there. Otherwise returns `None` and the cursor advances past
    /// the search window.
    ///
    /// This is the same as [`Cursor::find_next`]. The cursor only stops at
    /// leaf (frame) entries and never splits huge pages.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([`Cursor::find_next_panic_condition`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if a frame is found, the returned address equals the cursor's
    ///   current position, the owner is within the locked range, and the cursor level
    ///   is below the guard level.
    /// - **Correctness**: the found entry is always a frame (never a node or absent).
    ///   If the old entry at the same VA was also a frame, its `prop` field is preserved.
    /// - **Correctness**: if no entry is found, the cursor advances at least `len` bytes
    ///   past its starting position.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(owner, *old(regions), *old(guards)),
            // Delegates to `Cursor::find_next`, which diverges on the
            // find-next panic condition.
            old(self).0.find_next_panic_condition(len) ==> may_panic(),
        ensures
            !old(self).0.find_next_panic_condition(len),
            final(self).0.invariants_flat(final_owner@, *final(regions), *final(guards)),
            res is Some ==> {
                &&& res->0 == final(self).0.va
                &&& final_owner@.level <= final_owner@.guard_level
                &&& final_owner@.in_locked_range()
            },
    )]
    pub fn find_next<'owner: 'rcu>(&mut self, len: usize) -> Option<Vaddr> {
        proof_decl! {
            let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>;
        }
        #[verus_spec(with
            Tracked(owner), Tracked(regions), Tracked(guards) => Tracked(next_owner)
        )]
        let result = self.0.find_next(len);
        #[verus_spec(with |= Tracked(next_owner))]
        result
    }

    /// Jumps to the given virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    ///
    /// # Panics
    ///
    /// This method panics if the address is out of the range where the cursor is required to operate,
    /// or has bad alignment.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Correctness**: the function will panic if `va` is not page aligned
    ///   ([`Cursor::jump_panic_condition`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if `va` is within the barrier range, the result is `Ok` and the
    ///   cursor's VA is set to exactly `va`.
    /// - **Correctness**: if `va` is outside the barrier range, the result is `Err`.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).0.jump_panic_condition(va) ==> may_panic(),
        ensures
            !old(self).0.jump_panic_condition(va),
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(self).0.barrier_va.start <= va < final(self).0.barrier_va.end ==> {
                &&& res is Ok
                &&& final(self).0.va == va
            },
            !(final(self).0.barrier_va.start <= va < final(self).0.barrier_va.end) ==> res is Err,
    )]
    #[verifier::spinoff_prover]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError> {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.jump(va)
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.0.va,
    {
        self.0.virt_addr()
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants])
    /// must hold before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call
    /// - **Correctness**: if the cursor is within the locked range, the result will be `Ok`;
    /// otherwise it will be an error.
    /// - **Correctness**: if there is a mapping present ([Self::query_some_condition]),
    /// then the second field of the result will `Some(item)`, where `item` is the mapping,
    /// and the first field will give its range.
    /// - **Correctness**: if there is no mapping present, then the second field of the result will be
    /// 'None'.
    /// - **Safety**: all frames' relations with the metadata region are preserved.
    /// ## Safety
    /// - The global invariants ensure that the first node we pass through is already locked,
    /// and the loop invariant makes the same guarantee for subsequent nodes.
    /// - This function does not change anything in the metadata region except for incrementing
    /// the reference counts of nodes when it descends into them.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(owner, *old(regions), *old(guards)),
            // `in_locked_range` not required — delegates to the relaxed
            // `Cursor::query`, which handles out-of-range with `Err`. The
            // sole panic is cloning the resolved leaf frame when *that
            // specific slot* is saturated — precisely propagated from
            // `Cursor::query_panic_condition`.
            old(self).0.query_flat_panic_condition(owner, *old(regions)) ==> may_panic(),
        ensures
            final(self).0.invariants_flat(final_owner@, *final(regions), *final(guards)),
            !old(self).0.query_flat_panic_condition(owner, *old(regions)),
            owner.in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                final(self).0.query_flat_some_condition(final_owner@) ==>
                final(self).0.query_flat_some_ensures(final_owner@, state),
            res matches Ok(state) ==>
                !final(self).0.query_flat_some_condition(final_owner@) ==>
                final(self).0.query_flat_none_ensures(final_owner@, state),
            owner@.mappings == final_owner@@.mappings,
    )]
    pub fn query<'owner: 'rcu>(&mut self) -> (res: Result<PagesState<C>, PageTableError>) {
        proof_decl! { let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>; }
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards) => Tracked(next_owner))]
        let result = self.0.query();
        #[verus_spec(with |= Tracked(next_owner))]
        result
    }

    #[verus_spec(
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                 -> final_cursor_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(cursor_owner, *regions, *old(guards)),
            cursor_owner.in_locked_range(),
            cursor_owner.current_entry().is_node(),
            cursor_owner.resources.contains_raw_leased(cursor_owner.current_entry().child_paddr()),
            ChildRef::PageTable(pt).wf(cursor_owner.current_entry_decode_model()),
        ensures
            final(self).0.invariants_flat(final_cursor_owner@, *regions, *final(guards)),
            final_cursor_owner@.in_locked_range(),
            final_cursor_owner@.va == cursor_owner.va,
            final(self).0.level == old(self).0.level - 1,
            final(self).0.guard_level == old(self).0.guard_level,
            final(self).0.barrier_va == old(self).0.barrier_va,
            final_cursor_owner@.resources == cursor_owner.resources,
            final_cursor_owner@.as_page_table_owner() == cursor_owner.as_page_table_owner(),
            final_cursor_owner@.view_mappings() == cursor_owner.view_mappings(),
    )]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    fn map_branch_pt<'owner: 'rcu>(&mut self, pt: PageTableNodeRef<'rcu, C>, rcu_guard: &'rcu A) {
        let ghost before = cursor_owner;
        let ghost guards_before = *guards;
        proof {
            C::lemma_paging_consts_properties();
            cursor_owner.lemma_current_entry_inv(*regions);
            cursor_owner.as_page_table_owner().lemma_node_inv(
                cursor_owner.current_entry().child_paddr(),
            );
            assert(1 < cursor_owner.level);
            lemma_pte_index_bound::<C>(cursor_owner.va, (cursor_owner.level - 1) as PagingLevel);
            assert(!cursor_owner.is_path_node(cursor_owner.current_entry().child_paddr())) by {
                assert forall|key: int| cursor_owner.continuations.contains_key(key) implies
                    cursor_owner.continuations[key].node
                        != cursor_owner.current_entry().child_paddr() by {
                    assert(cursor_owner.continuation_inv(key));
                };
            };
        }
        let ghost child = cursor_owner.current_entry().child_paddr();
        // SAFETY: The `pt` must be locked and no other guards exist.
        let pt_guard = unsafe {
            let tracked record = cursor_owner.resources.tracked_borrow_record(child);
            #[verus_spec(with Tracked(&record.node), Tracked(guards))]
            pt.make_guard_unchecked(rcu_guard)
        };

        let ghost path = cursor_owner.current_entry().path;
        let ghost child_level = (cursor_owner.level - 1) as PagingLevel;
        let ghost idx = pte_index_spec::<C>(cursor_owner.va, child_level);
        let tracked cursor_owner = cursor_owner.tracked_push_leased_child(
            child, idx, path, child_level, pt_guard,
        );
        self.0.push_level(pt_guard);
        proof {
            assert(cursor_owner.inv());
            assert(self.0.wf_flat(cursor_owner));
            assert(cursor_owner.metaregion_sound(*regions));
            assert forall|key: int| #[trigger] cursor_owner.continuations.contains_key(key)
                implies guards.lock_held(cursor_owner.resources.leased_record(
                    cursor_owner.continuations[key].node).node.slot_vaddr()) by {
                if key != child_level - 1 {
                    assert(before.continuations.contains_key(key));
                    assert(before.continuation_inv(key));
                    assert(before.nodes_locked(guards_before));
                }
            };
            assert forall|paddr: Paddr| #[trigger]
                cursor_owner.as_page_table_owner().contains_node(paddr)
                    && !cursor_owner.is_path_node(paddr) implies
                guards.unlocked(cursor_owner.as_page_table_owner().node(paddr).node.slot_vaddr()) by {
                assert(paddr != child);
                assert(!before.is_path_node(paddr));
                assert(before.children_not_locked(guards_before));
                before.as_page_table_owner().lemma_node_inv(paddr);
                assert(before.as_page_table_owner().node(paddr).node.slot_vaddr()
                    != before.as_page_table_owner().node(child).node.slot_vaddr());
            };
        }
        #[verus_spec(with |= Tracked(cursor_owner))]
        ()
    }

    #[verifier::rlimit(300)]
    #[verus_spec(
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                 -> final_cursor_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(cursor_owner, *old(regions), *old(guards)),
            cursor_owner.in_locked_range(),
            level < old(self).0.guard_level,
            level >= 1,
        ensures
            final(self).0.invariants_flat(final_cursor_owner@, *final(regions), *final(guards)),
            final_cursor_owner@.va == cursor_owner.va,
            final(self).0.guard_level == old(self).0.guard_level,
            final(self).0.barrier_va == old(self).0.barrier_va,
            final(self).0.level == level,
            final_cursor_owner@.in_locked_range(),
            final_cursor_owner@@ == cursor_owner@.split_while_huge(page_size::<PagingConsts>(level)),
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *final(regions)),
            (level <= old(self).0.level && cursor_owner.cur_entry_owner().is_absent()) ==> final_cursor_owner@.cur_entry_owner().is_absent(),
            forall|idx: int|
                old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                (#[trigger] final(regions).slot_owners[idx]) == old(regions).slot_owners[idx],
            // `regions.slots` is monotonic — PT-node allocation removes-and-re-inserts
            // each slot it touches, so all old keys are preserved.
            forall|idx: int| #![trigger final(regions).slots.contains_key(idx)]
                old(regions).slots.contains_key(idx) ==> final(regions).slots.contains_key(idx),
    )]
    #[verifier::spinoff_prover]
    pub fn map_loop<'owner: 'rcu>(&mut self, level: PagingLevel, rcu_guard: &'rcu A) {
        let ghost owner0 = cursor_owner;
        let ghost guard_level = self.0.guard_level;
        let ghost barrier_va = self.0.barrier_va;
        let tracked mut owner = cursor_owner;

        #[verus_spec(
            invariant
                self.0.invariants_flat(owner, *regions, *guards),
                owner0.inv(),
                owner.va == owner0.va,
                self.0.guard_level == guard_level,
                self.0.barrier_va == barrier_va,
                1 <= level < self.0.guard_level,
                owner.in_locked_range(),
                owner@ == owner0@.split_while_huge(page_size::<PagingConsts>(self.0.level)),
                forall|item: C::Item|
                    #![trigger Self::item_slot_in_regions(item, *old(regions))]
                    Self::item_slot_in_regions(item, *old(regions)) ==>
                        Self::item_slot_in_regions(item, *regions),
                (self.0.level <= owner0.level && owner0.current_entry().is_absent()) ==>
                    owner.current_entry().is_absent(),
                self.0.level <= owner0.level || self.0.level <= level,
                self.0.level < level ==> self.0.level >= owner0.level,
                self.0.level < level ==> owner@ == owner0@,
                forall|idx: int|
                    #![trigger regions.slot_owners[idx], old(regions).ref_count(idx)]
                    old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                        regions.slot_owners[idx] == old(regions).slot_owners[idx],
                forall|idx: int| #![trigger regions.slots.contains_key(idx)]
                    old(regions).slots.contains_key(idx) ==> regions.slots.contains_key(idx),
            decreases abs(level - self.0.level),
        )]
        while self.0.level != level {
            if self.0.level < level {
                #[verus_spec(with Tracked(guards))]
                self.0.pop_level();
                proof {
                    owner.tracked_pop_level();
                }
                continue;
            }
            // We are at a higher level, go down.
            // Lease only the child permission, without moving a subtree.
            let tracked child_permission = if owner.current_entry().is_node() {
                let ghost child = owner.current_entry().child_paddr();
                let tracked (next_owner, permission) =
                    owner.tracked_lease_child_with_permission(child);
                owner = next_owner;
                Some(permission)
            } else {
                None
            };
            let mut cur_entry = {
                let tracked record = owner.tracked_borrow_current_record();
                #[verus_spec(with
                    Tracked(&record.node), Ghost(owner.current_entry_decode_model()),
                    Tracked(&*regions)
                )]
                self.0.cur_entry()
            };
            let cur_child = {
                let tracked metadata_permission = match child_permission {
                    Some(permission) => permission,
                    None => *cur_entry.node.inner.tracked_metadata_perm.borrow(),
                };
                let tracked record = owner.tracked_borrow_current_record();
                #[verus_spec(with
                    Ghost(owner.current_entry_decode_model()), Tracked(&record.node),
                    Tracked(regions), Tracked(metadata_permission)
                )]
                cur_entry.to_ref()
            };

            match cur_child {
                ChildRef::PageTable(pt) => {
                    proof_decl! {
                        let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>;
                    }
                    #[verus_spec(with
                        Tracked(owner), Tracked(&*regions), Tracked(guards)
                            => Tracked(next_owner)
                    )]
                    self.map_branch_pt(pt, rcu_guard);
                    proof {
                        owner = next_owner;
                    }
                },
                ChildRef::None => {
                    /* The hidden tracked return must be bound before unwrapping
                     * the executable Option.
                     * Origin Rust: let child_guard = cur_entry.alloc_if_none(rcu_guard).unwrap();
                     */
                    proof_decl! {
                        let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>;
                    }
                    #[verus_spec(with
                        Tracked(owner), Tracked(regions), Tracked(guards)
                            => Tracked(next_owner)
                    )]
                    let child_guard = cur_entry.alloc_if_none(rcu_guard);
                    let child_guard = child_guard.unwrap();
                    proof {
                        let ghost child = next_owner.current_entry().child_paddr();
                        let ghost path = next_owner.current_entry().path;
                        let ghost child_level = (next_owner.level - 1) as PagingLevel;
                        let ghost idx = pte_index_spec::<C>(next_owner.va, child_level);
                        owner = next_owner.tracked_push_leased_child(
                            child, idx, path, child_level, child_guard,
                        );
                    }
                    self.0.push_level(child_guard);
                },
                ChildRef::Frame(_, _, _) => {
                    /* The hidden tracked return must be bound before unwrapping
                     * the executable Option.
                     * Origin Rust: let split_child = cur_entry.split_if_mapped_huge(rcu_guard).unwrap();
                     */
                    proof_decl! {
                        let tracked next_owner: FlatCursorOwner<'owner, 'rcu, C>;
                    }
                    #[verus_spec(with
                        Tracked(owner), Tracked(regions), Tracked(guards)
                            => Tracked(next_owner)
                    )]
                    let split_child = cur_entry.split_if_mapped_huge(rcu_guard);
                    let split_child = split_child.unwrap();
                    proof {
                        let ghost child = next_owner.current_entry().child_paddr();
                        let ghost path = next_owner.current_entry().path;
                        let ghost child_level = (next_owner.level - 1) as PagingLevel;
                        let ghost idx = pte_index_spec::<C>(next_owner.va, child_level);
                        owner = next_owner.tracked_push_leased_child(
                            child, idx, path, child_level, split_child,
                        );
                    }
                    self.0.push_level(split_child);
                },
            }
        }
        #[verus_spec(with |= Tracked(owner))]
        ()
    }

    /// Maps the item starting from the current address to a physical address range.
    ///
    /// Writes a page-table entry for `item` at the cursor's current slot,
    /// descending through intermediate levels as needed. If the slot already
    /// contains a mapping, the old entry is replaced and returned as
    /// `Err(PageTableFrag)` for the caller to drop after TLB coherence.
    /// If the slot was absent, returns `Ok(())`.
    ///
    /// After the call the cursor has advanced past the mapped region.
    ///
    /// # Panics
    ///
    /// This function will panic if
    ///  - the virtual address range to be mapped is out of the locked range;
    ///  - the current virtual address is not aligned to the page size of the
    ///    item to be mapped.
    ///
    /// # Safety
    ///
    /// The caller should ensure that
    ///  - the range being mapped does not affect kernel's memory safety;
    ///  - the physical address to be mapped is valid and safe to use.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Safety**: the cursor must be within the locked range, below the
    ///   guard level, and before the barrier end ([`Self::map_cursor_requires`]).
    /// - **Correctness**: the entry owner must be valid and the item's level must
    ///   fit within the guard level ([`Self::item_wf`]).
    /// - **Safety**: the item's metadata slot must exist in the region
    ///   tracking structure ([`Self::item_slot_in_regions`]).
    /// - **Safety**: the function will panic if the VA is out of range or
    ///   misaligned for the item's page size ([`Self::map_panic_conditions`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: the abstract cursor view is updated by exactly the
    ///   `map_spec` operation — a single mapping is inserted at the current VA.
    /// - **Correctness**: if the cursor is still before the barrier end, it
    ///   remains ready for further map operations ([`Self::map_cursor_requires`]).
    /// - **Correctness**: if the old entry was absent, the result is `Ok(())`.
    /// - **Correctness**: `paths_in_pt` is preserved for all metadata slots
    ///   other than the newly mapped frame.
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(entry_owner): Tracked<EntryOwner<C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(cursor_owner, *old(regions), *old(guards)),
            old(self).item_wf(item, entry_owner),
            Self::item_slot_in_regions(item, *old(regions)),
            old(self).map_panic_conditions(item) ==> may_panic(),
        ensures
            !old(self).map_panic_conditions(item),
            final(self).0.invariants_flat(final_owner@, *final(regions), *final(guards)),
            old(self).map_item_ensures(
                item,
                cursor_owner@,
                final_owner@@,
            ),
            (C::item_into_raw(item).1 <= old(self).0.level
                && cursor_owner.current_entry_decode_model().is_absent()) ==> res.is_ok(),
            res is Err && res.unwrap_err() is StrayPageTable ==> C::item_into_raw(item).1 > 1,
            forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                old(regions).contains(idx) &&
                idx != frame_to_index(C::item_into_raw(item).0) &&
                old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                final(regions).slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt,
            forall|idx: int| #![trigger final(regions).slot_owners[idx].ref_count()]
                old(regions).contains(idx) &&
                old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                final(regions).ref_count(idx) != REF_COUNT_UNUSED,
            forall|idx: int| #![trigger final(regions).slot_owners[idx].ref_count()]
                old(regions).contains(idx) &&
                idx != frame_to_index(C::item_into_raw(item).0) &&
                old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                final(regions).ref_count(idx)
                    == old(regions).ref_count(idx),
            (C::item_into_raw(item).3@ is Some
                && old(regions).contains(frame_to_index(C::item_into_raw(item).0))
                && old(regions).ref_count(frame_to_index(C::item_into_raw(item).0)) > 0)
                ==>
                final(regions).ref_count(
                    frame_to_index(C::item_into_raw(item).0)) > 0,
            (C::item_into_raw(item).3@ is Some
                && old(regions).ref_count(
                    frame_to_index(C::item_into_raw(item).0))
                    <= REF_COUNT_MAX)
                ==>
                final(regions).ref_count(
                    frame_to_index(C::item_into_raw(item).0))
                    <= REF_COUNT_MAX,
            forall|idx: int| #![trigger final(regions).contains(idx)]
                old(regions).contains(idx) ==> final(regions).contains(idx),
            final(self).0.guard_level == old(self).0.guard_level,
            final(self).0.barrier_va == old(self).0.barrier_va,
    )]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    pub unsafe fn map<'owner: 'rcu>(&mut self, item: C::Item) -> (res: Result<(), PageTableFrag<C>>) {
        let ghost owner0 = cursor_owner;
        assert!(self.0.va < self.0.barrier_va.end);
        let (pa, level, prop, Tracked(raw_permission)) = C::item_into_raw(item);
        proof {
            C::lemma_paging_consts_properties();
            C::lemma_item_from_raw_roundtrip(item, pa, level, prop, Tracked(raw_permission));
        }
        assert!(level <= C::HIGHEST_TRANSLATION_LEVEL());
        assert!(level < self.0.guard_level);
        if !C::TOP_LEVEL_CAN_UNMAP() {
            assert!(level < NR_LEVELS as u8);
        }
        let size = page_size::<C>(level);
        assert_eq!(self.0.va % size, 0);
        let end = self.0.va + size;
        assert!(end <= self.0.barrier_va.end);

        let rcu_guard = self.0.rcu_guard;
        proof_decl! {
            let tracked mut owner: FlatCursorOwner<'owner, 'rcu, C>;
        }
        #[verus_spec(with
            Tracked(cursor_owner), Tracked(regions), Tracked(guards) => Tracked(owner)
        )]
        self.map_loop(level, rcu_guard);

        let ghost frame_path = owner.current_entry().path;
        let tracked new_owner = EntryOwner::tracked_new_frame(
            pa, frame_path, level, prop, raw_permission,
        );
        proof {
            let tracked slot = regions.tracked_borrow_mut_slot_owner(pa);
            slot.paths_in_pt = slot.paths_in_pt.insert(frame_path);
        }
        #[verus_spec(with Tracked(&mut owner), Tracked(new_owner), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));
        #[verus_spec(with Tracked(&mut owner), Tracked(&*regions), Tracked(guards))]
        self.0.move_forward_flat();

        #[verus_spec(with |= Tracked(owner))]
        if let Some(frag) = frag {
            Err(frag)
        } else {
            Ok(())
        }
    }

    /// Finds and removes the first page table entry in the following range.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes. If a mapped entry is found (frame or page-table subtree), it is
    /// removed and returned as a [`PageTableFrag`]. The cursor advances past
    /// the removed entry. If no mapped entries exist in the range, returns
    /// `None` and the cursor advances past the search window.
    ///
    /// The returned fragment is either `Mapped` (a single frame was removed)
    /// or `StrayPageTable` (an entire subtree was removed). The caller should
    /// handle TLB coherence before dropping the fragment.
    ///
    /// Internally calls `find_next_impl(len, true, true)`: it stops at the
    /// highest possible level for unmapping and splits huge pages as needed.
    ///
    /// # Safety
    ///
    /// The caller should ensure that the range being unmapped does not affect
    /// kernel's memory safety.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Safety**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([`Cursor::find_next_panic_condition`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: the cursor's VA never decreases, stays page-aligned, and
    ///   the barrier range is preserved.
    /// - **Correctness**: if an entry is found within `[old_va, old_va + len]`,
    ///   it is replaced by an absent entry, and the original entry is returned.
    /// - **Correctness**: if the entry represents a huge page whose size exceeds `len`,
    ///   it is split into pages at the next level and the first of those is replaced instead.
    /// - **Correctness**: the returned `StrayPageYable` has a `num_frames` field equal to
    ///   the number of removed mappings.
    /// - **Correctness**: if the result is `None`, there must have been no frames mapped in the range.
    /// - **Correctness**: if the result is `None`, the page table's abstract mappings are unchanged.
    /// ## Safety
    /// - It is always safe to unmap frames, but it is important to flush the TLB before mapping any
    ///   new frames in that range.
    /// - TODO: If this function is going to be called in a context where the stray page table will be
    ///   re-mapped or otherwise used for a purpose except flushing the TLB, we should also return
    ///   an owner object for that sub-tree.
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(cursor_owner, *old(regions), *old(guards)),
            old(self).0.find_next_panic_condition(len) ==> may_panic(),
        ensures
            !old(self).0.find_next_panic_condition(len),
            final(self).0.invariants_flat(final_owner@, *final(regions), *final(guards)),
            final(self).0.va >= old(self).0.va,
            final(self).0.va % PAGE_SIZE == 0,
            final(self).0.barrier_va == old(self).0.barrier_va,
            res is Some ==> final(self).0.va <= old(self).0.va + len,
            res is Some ==> final(self).0.va > old(self).0.va,
            res is Some ==> final_owner@.in_locked_range() || final_owner@.above_locked_range(),
            res is None ==> {
                &&& final_owner@@.cur_va >= (cursor_owner@.cur_va + len) as Vaddr
                &&& final_owner@@.mappings == cursor_owner@.mappings
                &&& cursor_owner@.mappings.filter(|m: Mapping|
                    cursor_owner@.cur_va <= m.va_range.start < (cursor_owner@.cur_va + len) as Vaddr) == Set::<Mapping>::empty()
            },
            res matches Some(PageTableFrag::Mapped { va, item }) ==> {
                let m = CursorView::<C>::item_into_mapping(va, item);
                let view = CursorView::<C> {
                    cur_va: va as Vaddr,
                    mappings: cursor_owner@.mappings,
                    phantom: PhantomData,
                };
                &&& cursor_owner@.mappings.filter(|m: Mapping|
                    old(self).0.va <= m.va_range.start < va) == Set::<Mapping>::empty()
                &&& final_owner@@.mappings.filter(|m2: Mapping|
                    va <= m2.va_range.start < final(self).0.va) == Set::<Mapping>::empty()
                // Splits only affect the entry at va; entries before it are untouched.
                &&& forall |m2: Mapping|
                    #![auto] final_owner@@.mappings.contains(m2) && old(self).0.va <= m2.va_range.start
                    && m2.va_range.start < va ==> cursor_owner@.mappings.contains(m2)
                &&& old(self).0.va <= va && (va as usize) < old(self).0.va + len
                &&& final_owner@@.mappings == view.split_while_huge(m.page_size).mappings - set![m]
                &&& view.split_while_huge(m.page_size).mappings.contains(m)
                &&& m.page_size >= PAGE_SIZE
            },
            res matches Some(PageTableFrag::StrayPageTable { va, len: len_frag, num_frames, .. }) ==> {
                let subtree = cursor_owner@.mappings.filter(
                    |m: Mapping| va <= m.va_range.start < va + len_frag);
                &&& cursor_owner@.mappings.filter(|m: Mapping|
                    old(self).0.va <= m.va_range.start < va) == Set::<Mapping>::empty()
                &&& final_owner@@.mappings.filter(|m2: Mapping|
                    va <= m2.va_range.start < final(self).0.va) == Set::<Mapping>::empty()
                // Entries before the removed subtree are untouched.
                &&& forall |m2: Mapping|
                    #![auto] final_owner@@.mappings.contains(m2) && old(self).0.va <= m2.va_range.start
                    && m2.va_range.start < va ==> cursor_owner@.mappings.contains(m2)
                &&& va >= old(self).0.va
                &&& va + len_frag <= old(self).0.va + len
                &&& final_owner@@.mappings == cursor_owner@.mappings.difference(subtree)
                &&& subtree.len() == num_frames as nat
            },
    )]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    pub unsafe fn take_next<'owner: 'rcu>(&mut self, len: usize) -> (r: Option<PageTableFrag<C>>) {
        proof_decl! {
            let tracked mut owner: FlatCursorOwner<'owner, 'rcu, C>;
        }
        #[verus_spec(with
            Tracked(cursor_owner), Tracked(regions), Tracked(guards) => Tracked(owner)
        )]
        let find_result = self.0.find_next_impl(len, true, true);
        if find_result.is_none() {
            return #[verus_spec(with |= Tracked(owner))]
            None;
        }

        let ghost removed_entry = owner.current_entry();
        let tracked absent = EntryOwner::tracked_new_absent(removed_entry.path, owner.level);
        #[verus_spec(with Tracked(&mut owner), Tracked(absent), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::None);
        #[verus_spec(with Tracked(&mut owner), Tracked(&*regions), Tracked(guards))]
        self.0.move_forward_flat();

        proof {
            if frag.unwrap() is Mapped {
                let tracked slot = regions.tracked_borrow_mut_slot_owner(removed_entry.frame().mapped_pa);
                slot.paths_in_pt = slot.paths_in_pt.remove(removed_entry.path);
            }
        }
        #[verus_spec(with |= Tracked(owner))]
        frag
    }

    /// Applies a property-changing operation to the next mapped frame in the range.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes looking for a mapped frame (using `find_next_impl` with
    /// `split_huge = true`). If found, applies `op` to the frame's
    /// [`PageProperty`], advances the cursor past it, and returns the
    /// protected VA range. If no mapped frame exists in the range, returns
    /// `None` and the cursor advances past the search window.
    ///
    /// # Safety
    ///
    /// The caller should ensure that:
    ///  - the range being protected with the operation does not affect
    ///    kernel's memory safety;
    ///  - the privileged flag `AVAIL1` should not be altered if in the kernel
    ///    page table (the restriction may be lifted in the future).
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([`Cursor::find_next_panic_condition`]).
    /// - **Correctness**: the current entry must be a frame, and `op` must be callable
    ///   on its current property (vacuously true unless we're verifying the caller).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// ## Safety
    /// - It is safe to call this function, but depending on the details of `op`, it may be necessary
    ///   to flush the TLB afterward. We do not model the behavior of `op`.
    ///
    /// Note: a previous version of this function had a postcondition asserting that the
    /// modified frame's mapping appears in `owner@.mappings` with the new property. That
    /// postcondition was structurally inconsistent with the split case (when find_next_impl
    /// splits a huge mapping, the resulting cursor frame is a sub-mapping NOT in the original
    /// `old(owner)@.mappings`), so it has been removed. A correct postcondition would
    /// reference `old(owner)@.split_while_huge(...).mappings` rather than `old(owner)@.mappings`.
    #[verifier::rlimit(200)]
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                -> final_cursor_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(self).0.invariants_flat(cursor_owner, *old(regions), *old(guards)),
            forall |p: PageProperty| op.requires((p,)),
            forall |pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty,
                perm: Tracked<Option<C::Perm>>| #![auto]
                op.ensures((p_in,), p_out) ==> (
                    C::item_into_raw(C::item_from_raw(pa, level, p_out, perm)).3@
                        is Some
                ) == (perm@ is Some),
            forall |pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty| #![auto]
                op.ensures((p_in,), p_out) && C::E::new_page_req(pa, level, p_in) ==>
                    C::E::new_page_req(pa, level, p_out),
            old(self).0.find_next_panic_condition(len) ==> may_panic(),
        ensures
            !old(self).0.find_next_panic_condition(len),
            final(self).0.invariants_flat(final_cursor_owner@, *final(regions), *final(guards)),
            final(self).0.barrier_va == old(self).0.barrier_va,
    )]
    pub unsafe fn protect_next<'owner: 'rcu>(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        proof_decl! {
            let tracked mut owner: FlatCursorOwner<'owner, 'rcu, C>;
        }
        /* Bind the hidden owner even on the early-return path.
         * Origin Rust: self.0.find_next_impl(len, false, true)?;
         */
        #[verus_spec(with
            Tracked(cursor_owner), Tracked(regions), Tracked(guards) => Tracked(owner)
        )]
        let found = self.0.find_next_impl(len, false, true);
        if found.is_none() {
            return #[verus_spec(with |= Tracked(owner))]
            None;
        }

        #[verus_spec(with Tracked(&mut owner), Tracked(regions), Tracked(guards))]
        self.protect_cur_entry(op);
        #[verus_spec(with Tracked(&owner))]
        let protected_va = self.0.cur_va_range_flat();
        #[verus_spec(with Tracked(&mut owner), Tracked(&*regions), Tracked(guards))]
        self.0.move_forward_flat();

        #[verus_spec(with |= Tracked(owner))]
        Some(protected_va)
    }

    /// Replaces the current entry with `new_child` and returns the old entry
    /// as a [`PageTableFrag`], or `None` if the old entry was absent.
    ///
    /// This is the low-level primitive used by [`Self::map`] and
    /// [`Self::take_next`]. It swaps the page-table entry at the cursor's
    /// current slot, updating the ghost ownership tree accordingly. The
    /// cursor position and level are unchanged after the call.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold,
    ///   with the owner in the locked range and not `popped_too_high`.
    /// - **New entry validity**: `new_owner` must be a valid ownership subtree at the
    ///   correct tree level and path, with `new_child.wf(new_owner.value)`.
    /// - **Disjointness**: every existing entry in the cursor's tree must have a
    ///   different physical metadata address than `new_owner.value`.
    /// - **Region tracking**: `new_owner.value` must already satisfy `metaregion_sound`.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: the abstract mappings are updated by removing the old
    ///   subtree's mappings and inserting `new_owner`'s mappings.
    /// - **Correctness**: the cursor's VA, level, guard level, and barrier range are
    ///   all unchanged.
    /// - **Correctness**: if the old entry was absent, `None` is returned; otherwise
    ///   `Some(frag)` is returned. A `Mapped` fragment carries the old frame's
    ///   paddr, level, and property. A `StrayPageTable` fragment carries the old
    ///   subtree's VA range and mapping count.
    /// - **Correctness**: `paths_in_pt` is preserved for all metadata slots except
    ///   the one belonging to `new_owner.value`.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut FlatCursorOwner<'_, 'rcu, C>>,
             Tracked(new_owner): Tracked<EntryOwner<C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            (!C::TOP_LEVEL_CAN_UNMAP_spec() && old(self).0.level >= NR_LEVELS && old(
                owner,
            ).current_entry_decode_model().is_node()) ==> may_panic(),
            old(self).0.invariants_flat(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            new_owner.inv(),
            !new_owner.is_node(),
            new_owner.parent_level == old(owner).level,
            new_owner.path == old(owner).current_entry().path,
            new_child.wf(new_owner),
            new_owner.metaregion_sound(*old(regions)),
        ensures
            res matches Some(PageTableFrag::StrayPageTable { .. }) && !C::TOP_LEVEL_CAN_UNMAP_spec()
                ==> old(owner).level < NR_LEVELS,
            final(owner)@.mappings == old(owner)@.mappings - old(owner).current_entry_mappings() + FlatEntryOwner::from_leaf_model(new_owner).leaf_mappings(),
            final(self).0.invariants_flat(*final(owner), *final(regions), *final(guards)),
            final(self).0.barrier_va == old(self).0.barrier_va,
            final(owner).va == old(owner).va,
            final(self).0.va == old(self).0.va,
            final(self).0.level == old(self).0.level,
            final(owner).guard_level == old(owner).guard_level,
            final(owner).in_locked_range(),
            old(owner).current_entry_decode_model().is_absent() ==> res is None,
            !old(owner).current_entry_decode_model().is_absent() ==> res is Some,
            res matches Some(PageTableFrag::Mapped { va, item }) ==> {
                let (pa, lvl, prop, _perm) = C::item_into_raw(item);
                &&& old(owner).current_entry_decode_model().is_frame()
                &&& va == old(self).0.va
                &&& lvl == old(self).0.level
                &&& pa == old(owner).current_entry_decode_model().frame().mapped_pa
                &&& prop == old(owner).current_entry_decode_model().frame().prop
            },
            res matches Some(PageTableFrag::StrayPageTable { va, len, num_frames, .. }) ==> {
                &&& va == old(self).0.va
                &&& len == page_size::<PagingConsts>(old(self).0.level)
                &&& old(owner).current_entry_decode_model().is_node()
                &&& num_frames as nat == old(owner).current_entry_mappings().len()
            },
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx].paths_in_pt]
                (new_owner.is_absent() || idx != frame_to_index(
                    new_owner.meta_slot_paddr()->0,
                )) ==> final(regions).slot_owners[idx].paths_in_pt == old(
                    regions,
                ).slot_owners[idx].paths_in_pt,
            forall|idx: int|
                #![trigger final(regions).contains(idx)]
                old(regions).contains(idx) ==> final(regions).contains(idx),
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx].ref_count()]
                final(regions).ref_count(idx) == old(regions).ref_count(idx),
            res is None ==> final(regions).slots == old(regions).slots,
            res matches Some(PageTableFrag::Mapped { .. }) && new_owner.is_absent() ==> forall|idx: int|
                #![trigger final(regions).slot_owners[idx]]
                final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
    )]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> Option<PageTableFrag<C>> {
        let ghost owner0 = *owner;
        let rcu_guard = self.0.rcu_guard;
        let va = self.0.va;
        let level = self.0.level;
        let entry_idx = pte_index::<C>(self.0.va, self.0.level);
        let ghost idx = entry_idx as int;

        let tracked old_entry = owner.tracked_borrow_current_record_mut().tracked_take_entry(idx);
        let tracked mut detached = None;
        let tracked mut root_entries = None;
        let tracked mut old_entry_owner = if old_entry.is_node() {
            let ghost child = old_entry.child_paddr();
            let ghost nodes = owner0.as_page_table_owner().subtree_nodes(child);
            let tracked (mut subtree, permission) =
                owner.resources.tracked_detach_unleased_subtree(child, nodes);
            let tracked record = subtree.nodes.tracked_remove(child);
            root_entries = Some(record.entries);
            detached = Some(subtree);
            EntryOwner {
                kind: crate::specs::mm::page_table::node::entry_owners::EntryOwnerKind::Node(record.node),
                node_permission: Some(permission),
                path: old_entry.path,
                parent_level: old_entry.parent_level,
            }
        } else {
            old_entry.tracked_into_leaf()
        };
        let tracked mut new_owner = new_owner;

        let old = {
            let node = path_slot_as_mut(&mut self.0.path, level as usize - 1);
            let tracked record = owner.tracked_borrow_current_record_mut();
            #[verus_spec(with
                Tracked(regions), Tracked(&mut old_entry_owner),
                Tracked(&mut new_owner), Tracked(&mut record.node),
            )]
            node.replace_child(entry_idx, new_child)
        };
        proof {
            let tracked entry = FlatEntryOwner::tracked_from_leaf(new_owner);
            owner.tracked_borrow_current_record_mut().tracked_set_entry(idx, entry);
        }

        match old {
            Child::None => None,
            Child::Frame(pa, ch_level, prop) => {
                let tracked raw_permission = old_entry_owner.tracked_take_frame_permission();
                // SAFETY: The replaced entry supplies the original raw mapping and
                // its linear frame permission, including for a split huge page.
                let item = unsafe { C::item_from_raw(pa, level, prop, Tracked(raw_permission)) };
                proof {
                    C::lemma_item_into_raw_roundtrip(pa, level, prop, Tracked(raw_permission));
                }
                Some(PageTableFrag::Mapped { va, item })
            },
            Child::PageTable(mut pt) => {
                if !C::TOP_LEVEL_CAN_UNMAP() && level as usize == NR_LEVELS {
                    let _ = ManuallyDrop::new(pt);
                    vstd_extra::panic::panic_diverge();
                }
                // The live Frame owns the root metadata permission again. The
                // flat detached store retains only structural/descendant resources.
                let tracked permission = old_entry_owner.tracked_take_node_permission();
                #[cfg(verus_keep_ghost_body)]
                {
                    pt.tracked_metadata_perm = Tracked(Some(permission));
                }
                let tracked mut subtree = match detached {
                    Some(subtree) => subtree,
                    None => { proof_from_false::<FlatDetachedSubtree<C>>() },
                };
                proof {
                    let tracked node = old_entry_owner.tracked_take_node();
                    let tracked entries = match root_entries {
                        Some(entries) => entries,
                        None => { proof_from_false::<Seq<FlatEntryOwner<C>>>() },
                    };
                    subtree.nodes.tracked_insert(subtree.root, FlatNodeRecord {
                        node, entries, path: old_entry.path,
                    });
                }

                let borrow_pt = pt.borrow();
                // SAFETY: The removed node belongs to the cursor's locked range.
                let locked_pt = unsafe {
                    #[verus_spec(with
                        Tracked(&subtree.nodes.tracked_borrow(subtree.root).node), Tracked(guards)
                    )]
                    borrow_pt.make_guard_unchecked(rcu_guard)
                };
                let ghost locked_addr = subtree.nodes[subtree.root].node.slot_vaddr();
                // SAFETY: Shared top-level nodes were excluded above; the
                // removed subtree is locked and no cursor guard refers to it.
                let num_frames = unsafe {
                    #[verus_spec(with
                        Tracked(&subtree), Tracked(guards), Ghost(locked_addr)
                    )]
                    locking::dfs_mark_stray_and_unlock(rcu_guard, &locked_pt)
                };
                Some(PageTableFrag::StrayPageTable {
                    pt: pt.into_dyn(), va,
                    len: page_size::<C>(self.0.level), num_frames,
                })
            },
        }
    }
}

} // verus!
