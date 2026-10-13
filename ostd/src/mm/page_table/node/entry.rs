// SPDX-License-Identifier: MPL-2.0
//! This module provides accessors to the page table entries in a node.
use vstd::{assert_maps_equal, assert_maps_equal_internal, prelude::*};
use vstd_extra::{ghost_tree::*, ownership::*};

use crate::specs::{
    arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::{
        frame::{
            frame_specs::FrameRawPerms,
            mapping::{frame_to_index, group_page_meta, max_meta_slots, meta_to_index},
            meta_region_owners::MetaRegionOwners,
        },
        page_table::{INC_LEVELS, PageTableOwner},
    },
    task::InAtomicMode,
};

use super::*;
use crate::arch::mm::PagingConsts;
use crate::mm::frame::meta::mapping::{frame_to_meta, meta_to_frame};
use crate::mm::frame::{
    Frame, FrameRef,
    meta::{REF_COUNT_MAX, REF_COUNT_UNUSED},
};
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::{
    mm::{nr_subpage_per_huge, nr_subpage_per_huge_spec, page_prop::PageProperty},
    //    sync::RcuDrop,
    //    task::atomic_mode::InAtomicMode,
};
use core::marker::PhantomData;
use core::ops::Deref;

verus! {

broadcast use group_ghost_tree_lemmas;

/// A reference to a page table node.
pub type PageTableNodeRef<'a, C> = FrameRef<'a, PageTablePageMeta<C>>;

/// A guard that holds the lock of a page table node.
pub struct PageTableGuard<'rcu, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Deref for PageTableGuard<'rcu, C> {
    type Target = PageTableNodeRef<'rcu, C>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

pub struct Entry<'a, 'rcu, C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    ///
    /// # Verification Design
    /// The concrete value of a PTE is specific to the architecture and the page table configuration,
    /// represented by the type `C::E`. We represent its value as an abstract [`EntryOwner`], which is
    /// connected to the concrete value by `match_pte`. The `EntryOwner` is well-formed with respect to
    /// `Entry` if it is related to the concrete value by `match_pte`.
    ///
    /// An `Entry` can be thought of as a mutable handle to the concrete value of the PTE.
    /// The `node` field is a mutable reference to the guard of the node that contains the entry,
    /// `index` provides the offset, and the `pte` is current value. Only one `Entry` can exist for
    /// a given node at any given time.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: &'a mut PageTableGuard<'rcu, C>,
}

#[verus_verify]
impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    pub open spec fn new_spec(
        pte: C::E,
        idx: usize,
        node: &'a mut PageTableGuard<'rcu, C>,
    ) -> Self {
        Self { pte, idx, node }
    }

    #[verus_spec(res =>
        ensures
            res.pte == pte,
            res.idx == idx,
            *res.node == *old(node),
            *final(node) == *final(res.node),
    )]
    pub fn new(pte: C::E, idx: usize, node: &'a mut PageTableGuard<'rcu, C>) -> Self {
        Self { pte, idx, node }
    }
}

#[verus_verify]
impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    /// Returns if the entry does not map to anything.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&EntryOwner<C>>,
        requires
            self.wf(*owner),
            owner.inv(),
        returns owner.is_absent(),
    )]
    pub(in crate::mm) fn is_none(&self) -> bool {
        !self.pte.is_present()
    }

    /// Returns if the entry maps to a page table node.
    #[verus_spec(
        with Tracked(owner): Tracked<EntryOwner<C>>,
             Tracked(parent_owner): Tracked<&NodeOwner<C>>,
        requires
            owner.inv(),
            self.wf(owner),
            parent_owner.relate_guard(*self.node),
            parent_owner.inv(),
            parent_owner.level() == owner.parent_level,
        returns
            owner.is_node(),
    )]
    pub(in crate::mm) fn is_node(&self) -> bool {
        self.pte.is_present() && !self.pte.is_last(
            #[verus_spec(with Tracked(Some(
                (*self.node.inner.tracked_metadata_perm.borrow()).tracked_borrow(),
            )))]
            self.node.level(),
        )
    }

    /// Gets a reference to the child.
    #[verus_spec(res =>
        with Ghost(owner): Ghost<EntryOwner<C>>,
             Tracked(parent_owner): Tracked<&NodeOwner<C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(metadata_permission): Tracked<&'rcu FracMetadataPerm>,
        requires
            self.invariants(owner, *old(regions)),
            self.node_matching(owner, *parent_owner, *self.node),
            parent_owner.metaregion_sound_node(*old(regions)),
            owner.is_node() ==> owner.node().permission_matches(*metadata_permission),
            owner.is_node() ==> {
                &&& owner.node_permission is Some
                &&& *metadata_permission == owner.node_permission()
            },
        ensures
            res.invariants(owner, *final(regions)),
            *final(regions) == *old(regions),
            final(regions).slot_owners == old(regions).slot_owners,
            forall|k: int|
                old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(
                    k,
                ),
            forall|k: int|
                old(regions).slots.contains_key(k) ==> old(regions).slots[k]
                    == #[trigger] final(regions).slots[k],
            final(regions).inv(),
    )]
    pub(in crate::mm) fn to_ref(&self) -> ChildRef<'rcu, C> {
        #[verus_spec(with Tracked(Some(
            (*self.node.inner.tracked_metadata_perm.borrow()).tracked_borrow(),
        )))]
        let level = self.node.level();

        // SAFETY:
        //  - The PTE outlives the reference (since we have `&self`).
        //  - The level matches the current node.
        let ghost before = *regions;
        let res = unsafe {
            #[verus_spec(with Tracked(regions), Ghost(owner), Tracked(metadata_permission))]
            ChildRef::from_pte(&self.pte, level)
        };
        proof {
            assert_maps_equal!(regions.slots, before.slots, key => {
                if regions.slots.contains_key(key) {
                    assert(0 <= key < max_meta_slots());
                    assert(before.slot_owners.contains_key(key));
                    assert(before.slots.contains_key(key));
                }
            });
            assert(*regions == before);
        }

        res
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The entry must satisfy the relevant safety invariants.
    /// - **Safety**: The entry must be a frame.
    /// ## Postconditions
    /// - **Safety Invariants**: The entry continues to satisfy the relevant safety invariants.
    /// - **Safety**: The guard permission is preserved.
    /// - **Correctness**: The entry's permissions are updated by `op`
    /// ## Safety
    /// - The entry is updated in place, only changing its properties.
    /// `regions` is passed read-only to source the parent node's slot perm
    /// via the borrow-model bridge (used by `write_pte`'s `start_paddr` call).
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut FlatEntryOwner<C>>,
             Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            old(owner).inv(),
            old(self).wf(old(owner).leaf_decode_model()),
            old(self).node_matching(old(owner).leaf_decode_model(), *old(parent_owner), *old(self).node),
            op.requires((old(self).pte.prop(),)),
            old(owner).is_frame(),
            regions.inv(),
            regions.slots.contains_key(old(parent_owner).slot_index),
            old(parent_owner).metaregion_sound_node(*regions),
            // `op` must preserve the trackedness of `item_from_raw(pa, level, _)`
            // across the prop change so frame-accounting guarantees remain unchanged.
            // For `KernelPtConfig`, `C::tracked(item)` reads `prop.flags.AVAIL1`, so this
            // precondition reduces to "op preserves AVAIL1". For `UserPtConfig`,
            // `C::tracked` is constant `true`, so this is trivial.
            forall|pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty,
                perm: Tracked<Option<C::Perm>>|
                #![auto]
                op.ensures((p_in,), p_out) ==> (
                    C::item_into_raw(C::item_from_raw(pa, level, p_out, perm)).3@
                        is Some
                ) == (perm@ is Some),
            forall|pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty|
                #![auto]
                op.ensures((p_in,), p_out) && C::E::new_page_req(pa, level, p_in)
                    ==> C::E::new_page_req(pa, level, p_out),
        ensures
            final(owner).inv(),
            final(self).wf(final(owner).leaf_decode_model()),
            final(self).node_matching(final(owner).leaf_decode_model(), *final(parent_owner), *final(self).node),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            final(owner).is_frame(),
            final(owner).frame().mapped_pa == old(owner).frame().mapped_pa,
            final(owner).frame_permission() == old(owner).frame_permission(),
            final(owner).frame_is_tracked() == old(owner).frame_is_tracked(),
            final(owner).path == old(owner).path,
            final(owner).parent_level == old(owner).parent_level,
            final(self).idx == old(self).idx,
            *final(self).node == *old(self).node,
            old(self).pte.is_present() ==> op.ensures(
                (old(owner).frame().prop,),
                final(owner).frame().prop,
            ),
            // `protect` only changes a present PTE's `prop` (never its
            // present-status) and never touches `nr_children`, so the present
            // count and the counter are both unchanged — keeping the parent's
            // `count_consistent` invariant intact for the caller.
            crate::specs::mm::page_table::node::owners::count_present(
                final(parent_owner).children_perm.value(),
            ) == crate::specs::mm::page_table::node::owners::count_present(
                old(parent_owner).children_perm.value(),
            ),
            final(parent_owner).meta_own.nr_children.value() == old(
                parent_owner,
            ).meta_own.nr_children.value(),
    )]
    pub(in crate::mm) fn protect(&mut self, op: impl FnOnce(PageProperty) -> PageProperty) {
        #[verus_spec(with Tracked(owner), Tracked(parent_owner), Tracked(regions))]
        let pte = self.node.protect_child(self.idx, op);
        self.pte = pte;
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: Both old and new owners must satisfy the respective safety invariants for an [Entry](Entry::invariants)
    /// and a [Child](Child::invariants).
    /// - **Safety**: The caller must provide valid owners for all objects, and for the parent node where the entry
    /// is being replaced. The parent node must have a valid guard permission.
    /// - **Correctness**: The new child must be compatible with the old, for instance by having the same level.
    /// ## Postconditions
    /// - **Safety Invariants**: The old and new owners will satisfy the safety invariants for an [Entry](Entry::invariants)
    /// and a [Child](Child::invariants), but they have changed positions.
    /// - **Safety**: Safety properties that hold across the page table's tree structure are preserved
    /// everywhere except for the entry being replaced.
    /// - **Correctness**: The entry will match the argument, and the returned child will match the entry that was replaced.
    /// ## Safety
    /// - The invariants ensure that the entry is appropriately aligned and its index is within bounds.
    /// - The transformation from child to entry ensures that the tree now owns the updated entry.
    #[verus_spec(res =>
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
             Tracked(owner): Tracked<&mut EntryOwner<C>>,
             Tracked(new_owner): Tracked<&mut EntryOwner<C>>,
             Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
        requires
            old(self).invariants(*old(owner), *old(regions)),
            new_child.invariants(*old(new_owner), *old(regions)),
            old(self).node_matching(*old(owner), *old(parent_owner), *old(self).node),
            old(self).new_owner_compatible(new_child, *old(owner), *old(new_owner), *old(regions)),
            old(parent_owner).metaregion_sound_node(*old(regions)),
        ensures
            final(self).invariants(*final(new_owner), *final(regions)),
            res.invariants(*final(owner), *final(regions)),
            final(self).node_matching(*final(new_owner), *final(parent_owner), *final(self).node),
            final(self).idx == old(self).idx,
            // Reborrowing `Entry` gives its nested mutable reference a new
            // identity. Relate their writeback values, not reference identity.
            mut_ref_future(old(self).node) == mut_ref_future(final(self).node),
            *final(self).node == *old(self).node,
            *final(owner) == old(owner).from_pte_owner_spec(),
            *final(new_owner) == old(new_owner).into_pte_owner_spec(),
            Self::metaregion_sound_neq_preserved(
                *old(owner),
                *final(new_owner),
                *old(regions),
                *final(regions),
            ),
            !final(new_owner).is_node() ==> Self::metaregion_sound_neq_old_preserved(
                *old(owner),
                *old(regions),
                *final(regions),
            ),
            (!old(owner).is_node() && !final(new_owner).is_node())
                ==> Self::metaregion_sound_preserved(*old(regions), *final(regions)),
            final(new_owner).is_node() && !final(new_owner).is_absent() ==> PageTableOwner::<
                C,
            >::path_tracked_pred(*final(regions))(*final(new_owner), final(new_owner).path),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            final(parent_owner).metaregion_sound_node(*final(regions)),
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx].paths_in_pt]
                (!final(new_owner).is_node() || final(new_owner).is_absent() || idx
                    != frame_to_index(final(new_owner).meta_slot_paddr()->0))
                    ==> final(regions).slot_owners[idx].paths_in_pt == old(
                    regions,
                ).slot_owners[idx].paths_in_pt,
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx].ref_count()]
                final(regions).ref_count(idx) == old(
                    regions,
                ).ref_count(idx),
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx].ref_count_perm]
                final(regions).slot_owners[idx].same_permissions(
                    old(regions).slot_owners[idx],
                ),
            final(regions).slots == old(regions).slots,
            // When both old and new are not nodes: from_pte/into_pte are identity.
            (!old(owner).is_node() && !final(new_owner).is_node()) ==> {
                &&& forall|i: int|
                    #![trigger final(regions).slot_owners[i]]
                    final(regions).slot_owners[i] == old(
                        regions,
                    ).slot_owners[i]
            },
            Self::replace_nonpanic_condition(*old(parent_owner), *old(new_owner)),
    )]
    #[verifier::spinoff_prover]
    pub(in crate::mm) fn replace(&mut self, new_child: Child<C>) -> Child<C> {
        let ghost cp0 = parent_owner.children_perm.value();
        let ghost initial_regions = *regions;
        let ghost initial_owner = *owner;
        let ghost initial_new_owner = *new_owner;

        #[cfg(feature = "allow_panic")]
        {
            let guard_level = self.node.level();
            match &new_child {
                Child::PageTable(node) => {
                    assert!(node.level() == guard_level - 1);
                },
                Child::Frame(_, level, _) => {
                    assert!(*level == guard_level);
                },
                Child::None => {},
            }
        }

        // SAFETY:
        //  - The PTE is not referenced by other `ChildRef`s (since we have `&mut self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(Some(
            (*self.node.inner.tracked_metadata_perm.borrow()).tracked_borrow(),
        )))]
        let level = self.node.level();

        let old_child = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(owner))]
            Child::from_pte(self.pte, level)
        };

        if old_child.is_none() && !new_child.is_none() {
            #[verus_spec(with
                Tracked(NodeOwner::<C>::tracked_borrow_frame_metadata_perm(
                    *self.node.inner.tracked_metadata_perm.borrow(),
                )),
                Ghost(parent_owner.meta_own.nr_children.id())
            )]
            let nr_children = self.node.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            proof {
                parent_owner.nr_children_absent_slot_bound(self.idx);
            }
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            #[verus_spec(with
                Tracked(NodeOwner::<C>::tracked_borrow_frame_metadata_perm(
                    *self.node.inner.tracked_metadata_perm.borrow(),
                )),
                Ghost(parent_owner.meta_own.nr_children.id())
            )]
            let nr_children = self.node.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            proof {
                parent_owner.nr_children_present_slot_bound(self.idx);
            }
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp - 1);
        }
        #[verus_spec(with Tracked(new_owner))]
        let new_pte = new_child.into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        //  3. The ownership of the child is passed to the page table node.
        unsafe {
            #[verus_spec(with Tracked(parent_owner), Tracked(&*regions))]
            self.node.write_pte(self.idx, new_pte)
        };

        self.pte = new_pte;

        proof {
            // Install new entry's path into its slot's paths_in_pt.
            // Nodes: singleton overwrite (tree enforces unique node path).
            // Frames: their path is installed by the caller BEFORE calling replace,
            //   so that `new_child.invariants` — which now requires
            //   `paths_in_pt.contains(new.path)` for the frame arm — is satisfied on
            //   entry. See the huge-page split and `replace_cur_entry` caller sites.
            if new_owner.is_node() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.lemma_contains_valid_frame_paddr(paddr);

                let tracked mut new_meta_slot = regions.tracked_borrow_mut_slot_owner(paddr);
                new_meta_slot.paths_in_pt = set![new_owner.path];
            }
        }

        proof {
            if new_owner.is_node() || new_owner.is_frame() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.lemma_contains_valid_frame_paddr(paddr);
            }
            if owner.is_frame() {
                let paddr = owner.frame().mapped_pa;
                let slot = frame_to_index(paddr);
                C::lemma_perm_well_formed_with_region_preserved(
                    paddr,
                    Tracked(owner.frame_permission()),
                    initial_regions,
                    *regions,
                );
            }
            if new_owner.is_frame() {
                let paddr = new_owner.frame().mapped_pa;
                let slot = frame_to_index(paddr);
                assert(initial_regions.slots[slot] == regions.slots[slot]);
                assert(initial_regions.slot_owners[slot].metadata_perm.id()
                    == regions.slot_owners[slot].metadata_perm.id());
                C::lemma_perm_well_formed_with_region_preserved(
                    paddr,
                    Tracked(new_owner.frame_permission()),
                    initial_regions,
                    *regions,
                );
            }
            assert(Self::metaregion_sound_neq_preserved(
                initial_owner,
                *new_owner,
                initial_regions,
                *regions,
            )) by {
                let f = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.meta_slot_paddr_neq(initial_owner) && entry.meta_slot_paddr_neq(
                        *new_owner,
                    ) && entry.metaregion_sound(initial_regions);
                let g = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.metaregion_sound(*regions);
                assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                    if entry.is_frame() {
                        let paddr = entry.frame().mapped_pa;
                        C::lemma_perm_well_formed_with_region_preserved(
                            paddr,
                            Tracked(entry.frame_permission()),
                            initial_regions,
                            *regions,
                        );
                    }
                };
            };
            crate::specs::mm::page_table::node::owners::lemma_count_present_upto_update(
                cp0,
                NR_ENTRIES as int,
                self.idx as int,
                new_pte,
            );
        }

        old_child
    }

    /// Allocates an absent child directly into the cursor's flat owner map.
    ///
    /// The allocated frame is converted to raw form before the returned guard
    /// is built.  Its metadata permission is parked in the flat map and the
    /// guard borrows that stable map entry.
    #[verifier::spinoff_prover]
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                 -> final_cursor_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(regions).inv(),
            cursor_owner.inv(),
            cursor_owner.metaregion_sound(*old(regions)),
            cursor_owner.continuations.contains_key(cursor_owner.level - 1),
            cursor_owner.resources.contains_leased(cursor_owner.current_paddr()),
            cursor_owner.current().idx == old(self).idx,
            cursor_owner.current().guard == *old(self).node,
            cursor_owner.current_entry().match_pte(old(self).pte),
            cursor_owner.current_record().node.relate_guard(*old(self).node),
            cursor_owner.current_record().node.level == cursor_owner.level,
        ensures
            res is None ==> final_cursor_owner@ == cursor_owner,
            res is Some ==> {
                &&& final_cursor_owner@.current_entry().is_node()
                &&& final_cursor_owner@.resources.contains_raw_leased(
                    final_cursor_owner@.current_entry().child_paddr(),
                )
                &&& final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).relate_guard(res->0)
                &&& final(guards).lock_held(res->0.inner.inner@.ptr.addr())
            },
            final(regions).inv(),
            final(self).idx == old(self).idx,
            forall|i: usize| old(guards).lock_held(i) ==> final(guards).lock_held(i),
    )]
    pub(in crate::mm) fn alloc_if_none<'owner: 'rcu, A: InAtomicMode>(
        &mut self,
        guard: &'rcu A,
    ) -> Option<PageTableGuard<'rcu, C>> {
        proof {
            C::lemma_paging_consts_properties();
            cursor_owner.lemma_current_entry_inv(*regions);
        }
        let entry_is_present = self.pte.is_present();
        let tracked metadata_perm = (
        *self.node.inner.tracked_metadata_perm.borrow()).tracked_borrow();
        #[verus_spec(with Tracked(Some(metadata_perm)))]
        let level = self.node.level();

        if entry_is_present || level <= 1 {
            return #[verus_spec(with |= Tracked(cursor_owner))]
            None;
        }
        let ghost child_path = cursor_owner.current_entry().path;
        let ghost cp0 = cursor_owner.current_record().node.children_perm.value();
        let ghost regions_before_alloc = *regions;
        proof {
            cursor_owner.current_record().node.nr_children_absent_slot_bound(self.idx);
        }

        proof_decl! {
            let tracked new_record: FlatNodeRecord<C>;
        }
        #[verus_spec(with
            Tracked(regions),
            Tracked(guards),
            Ghost(child_path)
                => Tracked(new_record)
        )]
        let new_page = PageTableNode::<C>::alloc(level - 1);
        let paddr = new_page.start_paddr();
        proof {
            cursor_owner.lemma_fresh_node_can_insert(paddr, regions_before_alloc);
        }
        let ghost new_slot_index = new_record.node.slot_index;

        proof_decl! {
            let tracked raw_perms: FrameRawPerms;
        }
        let raw_paddr = #[verus_spec(with => Tracked(raw_perms))]
        new_page.into_raw();
        self.pte = C::E::new_pt(raw_paddr);

        let tracked (new_cursor_owner, stable_permission) =
            cursor_owner.tracked_attach_current_and_lease_child_with_permission(
            new_record,
            raw_perms.metadata_perm,
        );
        let tracked mut cursor_owner = new_cursor_owner;
        let ghost child_record = cursor_owner.resources.leased_record(paddr);

        let tracked slot_perm = *regions.slots.tracked_borrow(new_slot_index);
        let pt_ref = unsafe {
            #[verus_spec(with Tracked(slot_perm), Tracked(stable_permission))]
            PageTableNodeRef::borrow_paddr(paddr)
        };
        let pt_lock_guard = {
            let tracked record = cursor_owner.resources.tracked_borrow_record(paddr);
            #[verus_spec(with Tracked(&record.node), Tracked(guards))]
            pt_ref.lock(guard)
        };

        unsafe {
            let tracked parent_record = cursor_owner.tracked_borrow_current_record_mut();
            #[verus_spec(with Tracked(&mut parent_record.node), Tracked(&*regions))]
            self.node.write_pte(self.idx, self.pte)
        };

        {
            let tracked parent_record = cursor_owner.tracked_borrow_current_record_mut();
            let tracked parent_metadata_perm = (
            *self.node.inner.tracked_metadata_perm.borrow()).tracked_borrow();
            #[verus_spec(with
                Tracked(parent_metadata_perm),
                Ghost(parent_record.node.meta_own.nr_children.id())
            )]
            let nr_children = self.node.nr_children_mut();
            let old_nr_children = nr_children.read(
                Tracked(&parent_record.node.meta_own.nr_children),
            );
            nr_children.write(
                Tracked(&mut parent_record.node.meta_own.nr_children),
                old_nr_children + 1,
            );
            proof {
                crate::specs::mm::page_table::node::owners::lemma_count_present_upto_update(
                    cp0,
                    NR_ENTRIES as int,
                    self.idx as int,
                    self.pte,
                );
            }
        }

        proof {
            assert(cursor_owner.current_entry().child_paddr() == paddr);
            assert(cursor_owner.resources.contains_raw_leased(paddr));
            assert(cursor_owner.resources.leased_record(paddr) == child_record);
            assert(cursor_owner.resources.leased_record(paddr).relate_guard(pt_lock_guard));
            regions.lemma_contains_valid_frame_paddr(paddr);
            let tracked new_meta_slot = regions.tracked_borrow_mut_slot_owner(paddr);
            new_meta_slot.paths_in_pt = set![child_path];
        }

        #[verus_spec(with |= Tracked(cursor_owner))]
        Some(pt_lock_guard)
    }

    /// Splits the entry to smaller pages if it maps to a huge page.
    ///
    /// If the entry does map to a huge page, it is split into smaller pages
    /// mapped by a child page table node. The new child page table node
    /// is returned.
    ///
    /// If the entry does not map to a untracked huge page, the method returns
    /// `None`.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The old node's root must satisfy the safety invariants for an [Entry](Entry::invariants)
    /// and the caller must provide its parent node owner.
    /// ## Postconditions
    /// - **Safety Invariants**: The node allocated in place of the split page satisfies the safety invariants.
    /// - **Safety**: All other nodes have their invariants preserved.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    #[verus_spec(res =>
        with Tracked(cursor_owner): Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&mut Guards>,
                 -> final_cursor_owner: Tracked<FlatCursorOwner<'owner, 'rcu, C>>,
        requires
            old(regions).inv(),
            cursor_owner.inv(),
            cursor_owner.metaregion_sound(*old(regions)),
            cursor_owner.continuations.contains_key(cursor_owner.level - 1),
            cursor_owner.resources.contains_leased(cursor_owner.current_paddr()),
            cursor_owner.current().idx == old(self).idx,
            cursor_owner.current().guard == *old(self).node,
            cursor_owner.current_entry().match_pte(old(self).pte),
            cursor_owner.current_record().node.relate_guard(*old(self).node),
            cursor_owner.current_record().node.level == cursor_owner.level,
            cursor_owner.level < NR_LEVELS,
        ensures
            final_cursor_owner@.resources.inv(),
            final_cursor_owner@.as_page_table_owner().inv(),
            final_cursor_owner@.inv(),
            cursor_owner.metaregion_sound(*final(regions)),
            final_cursor_owner@.metaregion_sound(*final(regions)),
            (res is Some) == (cursor_owner.current_entry().is_frame() && cursor_owner.level > 1),
            res is Some && cursor_owner.in_locked_range() ==>
                final_cursor_owner@.view().mappings == cursor_owner.view().split_if_mapped_huge_spec(
                    page_size::<C>((cursor_owner.level - 1) as PagingLevel)).mappings,
            final_cursor_owner@.root == cursor_owner.root,
            final_cursor_owner@.level == cursor_owner.level,
            final_cursor_owner@.guard_level == cursor_owner.guard_level,
            final_cursor_owner@.va == cursor_owner.va,
            final_cursor_owner@.prefix == cursor_owner.prefix,
            final_cursor_owner@.barrier_va == cursor_owner.barrier_va,
            final_cursor_owner@.popped_too_high == cursor_owner.popped_too_high,
            final_cursor_owner@.continuations == cursor_owner.continuations,
            final_cursor_owner@.current_record().entries.len() == cursor_owner.current_record().entries.len(),
            final_cursor_owner@.current_entry().path == cursor_owner.current_entry().path,
            res is None ==> final_cursor_owner@ == cursor_owner,
            res is Some ==> {
                &&& res is Some
                &&& final_cursor_owner@.current_entry().is_node()
                &&& cursor_owner.as_page_table_owner().leaf_node_insert(
                    final_cursor_owner@.as_page_table_owner(), cursor_owner.current_paddr(),
                    cursor_owner.current().idx as int, final_cursor_owner@.current_entry().child_paddr())
                &&& final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).local_inv()
                &&& final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).path == cursor_owner.current_entry().path
                &&& final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).node.level + 1 == cursor_owner.level
                &&& **res->0.inner.tracked_metadata_perm == *final_cursor_owner@.resources.leases[
                    final_cursor_owner@.current_entry().child_paddr()].permission
                &&& final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).node.metaregion_sound(*final_cursor_owner@.resources.leases[
                    final_cursor_owner@.current_entry().child_paddr()].permission, *final(regions))
                &&& final(regions).slot_owners[final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).node.slot_index].paths_in_pt == set![cursor_owner.current_entry().path]
                &&& final_cursor_owner@.resources.contains_raw_leased(
                    final_cursor_owner@.current_entry().child_paddr(),
                )
                &&& final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).relate_guard(res->0)
                &&& final(guards).lock_held(res->0.inner.inner@.ptr.addr())
                &&& forall|j: int| #![trigger final_cursor_owner@.resources.leased_record(
                    final_cursor_owner@.current_entry().child_paddr(),
                ).entries[j]] 0 <= j < NR_ENTRIES ==> {
                    let child = final_cursor_owner@.resources.leased_record(
                        final_cursor_owner@.current_entry().child_paddr(),
                    ).entries[j];
                    &&& child.is_frame()
                    &&& child.frame().prop == cursor_owner.current_entry().frame().prop
                    &&& child.frame().mapped_pa == cursor_owner.current_entry().frame().mapped_pa
                        + j * page_size::<C>((cursor_owner.level - 1) as PagingLevel)
                    &&& child.frame_permission() is None
                }
                &&& forall |j: int| 0 <= j < NR_ENTRIES ==>
                    #[trigger] final_cursor_owner@.resources.leased_record(
                        final_cursor_owner@.current_entry().child_paddr(),
                    ).entries[j].parent_level == cursor_owner.level - 1
            },
            final(self).idx == old(self).idx,
            final(regions).inv(),
            final(self).node.inner.inner@.ptr.addr() == old(self).node.inner.inner@.ptr.addr(),
            mut_ref_future(old(self).node) == mut_ref_future(final(self).node),
            *final(self).node == *old(self).node,
            forall |i: usize| old(guards).lock_held(i) ==> final(guards).lock_held(i),
            forall |i: usize| old(guards).unlocked(i)
                && (res is None || i != res->0.inner.inner@.ptr.addr())
                ==> final(guards).unlocked(i),
    )]
    pub(in crate::mm) fn split_if_mapped_huge<'owner: 'rcu, A: InAtomicMode>(
        &mut self,
        guard: &'rcu A,
    ) -> Option<PageTableGuard<'rcu, C>> {
        proof {
            C::lemma_paging_consts_properties();
            cursor_owner.lemma_current_entry_inv(*regions);
        }
        let tracked node_metadata_perm = (
        *self.node.inner.tracked_metadata_perm.borrow()).tracked_borrow();
        #[verus_spec(with Tracked(Some(node_metadata_perm)))]
        let level = self.node.level();

        if !(self.pte.is_last(level) && level > 1) {
            return #[verus_spec(with |= Tracked(cursor_owner))]
            None;
        }
        let pa = self.pte.paddr();
        let prop = self.pte.prop();
        let ghost huge_entry = cursor_owner.current_entry().leaf_decode_model();
        let ghost original_owner = cursor_owner;
        proof {
            C::lemma_huge_raw_item_untracked(
                pa, level, prop, Tracked(huge_entry.frame_permission()),
            );
            EntryOwner::<C>::axiom_frame_is_tracked_iff_not_mmio(huge_entry);
        }
        let ghost regions_before_alloc = *regions;
        let ghost child_path = cursor_owner.current_entry().path;

        proof_decl! {
            let tracked new_record: FlatNodeRecord<C>;
        }
        #[verus_spec(with
            Tracked(regions),
            Tracked(guards),
            Ghost(child_path)
                => Tracked(new_record)
        )]
        /* The inherited RcuDrop migration is intentionally out of scope.
         * Origin Rust:
         * let new_page = RcuDrop::new(PageTableNode::<C>::alloc(level - 1));
         */
        let mut new_page = PageTableNode::<C>::alloc(level - 1);
        proof {
            new_record.lemma_allocated_empty_inv((level - 1) as PagingLevel, child_path);
        }
        let paddr = new_page.start_paddr();
        proof {
            cursor_owner.lemma_fresh_node_can_insert(paddr, regions_before_alloc);
        }

        // Only the ghost metadata token is lent to a stable slot. The live
        // Frame is not consumed, and the structural record is not attached
        // to the parent while its child entries are being initialized.
        let tracked permission = new_page.tracked_metadata_perm.tracked_take();
        proof {
            regions.slot_owners.tracked_borrow(new_record.node.slot_index)
                .metadata_perm.validate_with_frac(&permission);
        }
        let tracked slot_perm = *new_page.tracked_slot_perm.borrow();
        let tracked FlatCursorOwner {
            resources,
            continuations,
            root,
            level: cursor_level,
            guard_level,
            va,
            prefix,
            barrier_va,
            popped_too_high,
        } = cursor_owner;
        let ghost parent_paddr = continuations[cursor_level - 1].node;
        let tracked (mut resources, loan) = resources.tracked_lend_node_permission(
            paddr,
            permission,
        );
        proof {
            reveal(crate::specs::mm::page_table::FlatCursorResources::inv);
            assert(resources.inv());
        }

        // SAFETY: The live node is retained until Child::into_pte below.
        // Its metadata loan remains valid for the returned guard's lifetime.
        let pt_ref = unsafe {
            #[verus_spec(with Tracked(slot_perm), Tracked(loan.permission))]
            PageTableNodeRef::borrow_paddr(paddr)
        };

        // Lock before writing the parent PTE, as in the original Rust.
        let ghost guards_before_lock = *guards;
        #[verus_spec(with Tracked(&new_record.node), Tracked(guards))]
        let mut pt_lock_guard = pt_ref.lock(guard);

        proof {
            C::lemma_paging_consts_properties();
            assert(nr_subpage_per_huge_spec::<C>() == NR_ENTRIES);
            original_owner.as_page_table_owner().lemma_node_inv(root);
            assert(parent_paddr != resources.root.paddr);
        }

        for i in 0..nr_subpage_per_huge::<C>()
            invariant
                nr_subpage_per_huge_spec::<C>() == NR_ENTRIES,
                0 <= i <= NR_ENTRIES,
                1 < level < NR_LEVELS,
                C::NR_LEVELS() == NR_LEVELS,
                huge_entry.inv(),
                huge_entry.is_frame(),
                huge_entry.parent_level == level,
                huge_entry.frame().mapped_pa == pa,
                huge_entry.frame().prop == prop,
                huge_entry.frame_permission() is None,
                crate::specs::mm::frame::meta_owners::is_mmio_paddr(pa),
                resources.can_insert_raw_node(paddr),
                resources.inv(),
                resources.owner_view() == original_owner.as_page_table_owner(),
                original_owner.inv(),
                original_owner.level == level,
                original_owner.current_paddr() == parent_paddr,
                parent_paddr != resources.root.paddr,
                regions_before_alloc.inv(),
                original_owner.metaregion_sound(regions_before_alloc),
                valid_frame_paddr(paddr),
                !crate::specs::mm::frame::meta_owners::is_mmio_paddr(paddr),
                regions_before_alloc.ref_count(frame_to_index(paddr)) == REF_COUNT_UNUSED,
                forall|key: int| #[trigger] regions_before_alloc.slots.contains_key(key)
                    && key != frame_to_index(paddr) ==> {
                    &&& regions.slots[key] == regions_before_alloc.slots[key]
                    &&& regions.slot_owners[key].same_permissions(regions_before_alloc.slot_owners[key])
                    &&& regions.slot_owners[key].usage == regions_before_alloc.slot_owners[key].usage
                    &&& regions_before_alloc.slot_owners[key].paths_in_pt.subset_of(regions.slot_owners[key].paths_in_pt)
                    &&& regions_before_alloc.slot_owners[key].usage is PageTable ==>
                        regions.slot_owners[key].paths_in_pt == regions_before_alloc.slot_owners[key].paths_in_pt
                },
                new_record.paddr() == paddr,
                new_record.node.level == level - 1,
                new_record.node.relate_guard(pt_lock_guard),
                new_record.node.permission_matches(*loan.permission),
                **pt_lock_guard.inner.tracked_metadata_perm == *loan.permission,
                new_record.node.count_consistent(),
                new_record.node.metaregion_sound_node(*regions),
                new_record.node.metaregion_sound(*loan.permission, *regions),
                regions.ref_count(frame_to_index(paddr)) == 1,
                new_record.local_inv(),
                new_record.path == child_path,
                new_record.entries.len() == NR_ENTRIES,
                forall|j: int| i <= j < NR_ENTRIES ==> #[trigger] new_record.entries[j].is_absent(),
                forall|j: int| 0 <= j < i ==> #[trigger] new_record.entries[j].is_frame(),
                forall|j: int| 0 <= j < i ==> #[trigger] new_record.entries[j].frame().prop == prop,
                forall|j: int| 0 <= j < i ==> #[trigger] new_record.entries[j].frame().mapped_pa
                    == pa + j * page_size::<C>((level - 1) as PagingLevel),
                forall|j: int| 0 <= j < i ==> #[trigger] new_record.entries[j].frame_permission() is None,
                forall|j: int| 0 <= j < i ==> #[trigger] new_record.entries[j].metaregion_sound(*regions),
                forall|j: int|
                    0 <= j < NR_ENTRIES ==> #[trigger] new_record.entries[j].parent_level == level
                        - 1,
                regions.inv(),
                guards.lock_held(new_record.node.slot_vaddr()),
                PageTableNodeRef::<C>::locks_preserved_except(
                    new_record.node.slot_vaddr(), guards_before_lock, *guards,
                ),
        {
            proof {
                C::lemma_paging_consts_properties();
                huge_entry.huge_frame_split_child_at(*regions, i);
            }
            let ghost regions_before_subpage = *regions;
            let ghost entries_before_subpage = new_record.entries;
            let small_pa = pa + i * page_size::<C>(level - 1);
            let ghost entry_path = new_record.entries[i as int].path;

            proof {
                C::lemma_raw_item_well_formed_split(pa, level, prop, small_pa, i, Tracked(None));
                C::lemma_none_perm_well_formed(small_pa, *regions);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();
                regions.lemma_contains_valid_frame_paddr(small_pa);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_next::<C>(
                    (level - 1) as PagingLevel,
                );
                vstd::arithmetic::mul::lemma_mul_strict_inequality(
                    i as int, NR_ENTRIES as int,
                    page_size::<C>((level - 1) as PagingLevel) as int,
                );
                crate::specs::mm::frame::meta_owners::axiom_mmio_paddr_huge_page_closed(
                    pa, page_size::<C>(level),
                    (i * page_size::<C>((level - 1) as PagingLevel)) as usize,
                );
                crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr(
                    regions.slot_owner(small_pa),
                );
                let tracked small_slot = regions.tracked_borrow_mut_slot_owner(small_pa);
                small_slot.paths_in_pt = small_slot.paths_in_pt.insert(entry_path);
            }

            // These leaf-only owners adapt the remaining legacy Entry API.
            // No subtree is constructed or converted; the real frame
            // permission returns to the flat entry immediately afterwards.
            let tracked mut old_owner = EntryOwner::tracked_new_absent(
                entry_path,
                (level - 1) as PagingLevel,
            );
            let tracked mut new_owner = EntryOwner::tracked_new_frame(
                small_pa,
                entry_path,
                (level - 1) as PagingLevel,
                prop,
                None,
            );
            proof {
                assert(new_record.entries[i as int].is_absent());
                assert(new_record.entries[i as int].match_pte(
                    new_record.node.children_perm.value()[i as int],
                ));
                assert(!new_record.node.children_perm.value()[i as int].is_present());
                assert(new_owner.inv());
                assert(regions.inv());
                C::lemma_none_perm_well_formed(small_pa, *regions);
                let child_size = page_size::<PagingConsts>((level - 1) as PagingLevel);
                assert(child_size == 4096 || child_size == 2097152);
                assert forall|j: usize|
                    #![trigger frame_to_index((small_pa + j * PAGE_SIZE) as usize)]
                    0 < j < child_size / PAGE_SIZE implies
                        regions.slots.contains_key(frame_to_index(
                            (small_pa + j * PAGE_SIZE) as usize,
                        )) by {
                    assert(j * PAGE_SIZE < child_size) by(nonlinear_arith)
                        requires j < child_size / PAGE_SIZE,
                            child_size == 4096 || child_size == 2097152,
                            PAGE_SIZE == 4096;
                    let sub_pa = (small_pa + j * PAGE_SIZE) as usize;
                    assert(crate::specs::arch::valid_frame_paddr(sub_pa));
                    regions.lemma_contains_valid_frame_paddr(sub_pa);
                };
                assert(new_owner.metaregion_sound(*regions));
            }
            #[verus_spec(with
                Tracked(&new_record.node), Ghost(old_owner), Tracked(&*regions)
            )]
            let mut entry = pt_lock_guard.entry(i);
            #[verus_spec(with
                Tracked(regions), Tracked(&mut old_owner), Tracked(&mut new_owner),
                Tracked(&mut new_record.node)
            )]
            let old = entry.replace(Child::Frame(small_pa, level - 1, prop));
            debug_assert!(old.is_none());

            proof {
                assert(new_record.node.relate_guard(*entry.node));
                let ghost written_model = new_owner;
                let tracked frame = match new_owner.kind {
                    EntryOwnerKind::Frame(frame) => frame,
                    _ => proof_from_false(),
                };
                new_record.tracked_set_entry(
                    i as int,
                    FlatEntryOwner {
                        kind: FlatEntryOwnerKind::Frame(frame),
                        path: entry_path,
                        parent_level: (level - 1) as PagingLevel,
                    },
                );
                assert(new_record.node.relate_guard(*entry.node));
                assert forall|j: int| 0 <= j <= i implies
                    #[trigger] new_record.entries[j].metaregion_sound(*regions) by {
                    let current = new_record.entries[j];
                    C::lemma_none_perm_well_formed(current.frame().mapped_pa, *regions);
                    if j < i {
                        assert(current == entries_before_subpage[j]);
                        assert(current.metaregion_sound(regions_before_subpage));
                        C::lemma_perm_well_formed_with_region_preserved(
                            current.frame().mapped_pa, Tracked(current.frame_permission()),
                            regions_before_subpage, *regions);
                    } else {
                        assert(current.leaf_decode_model() == written_model);
                        assert(written_model.metaregion_sound(*regions));
                    }
                };
            }
        }

        // The live Frame is consumed at the original Rust boundary, only
        // after all child PTEs have been initialized. The legacy Child API
        // temporarily carries the same structural node owner, with no second
        // metadata token; the existing loan is adopted by the raw-node lease.
        let ghost root_record_before_publish = *resources.root.record;
        let ghost initialized_entries = new_record.entries;
        let ghost regions_before_publish = *regions;
        let tracked FlatNodeRecord { node, entries, path } = new_record;
        let tracked mut pte_owner = EntryOwner::tracked_new_node(node, None, path);
        self.pte = #[verus_spec(with Tracked(&mut pte_owner))]
        Child::PageTable(new_page).into_pte();

        let tracked node = pte_owner.tracked_take_node();
        let tracked new_record = FlatNodeRecord { node, entries, path };
        proof {
            // Publishing the flat edge also publishes the node's metadata path.
            // The live Frame kept the permission until Child::into_pte above.
            let tracked new_slot = regions.tracked_borrow_mut_slot_owner(paddr);
            new_slot.paths_in_pt = set![child_path];
        }
        let tracked mut resources = resources.tracked_insert_lent_node(new_record, loan);
        let ghost parent_permission = *resources.leases[parent_paddr].permission;
        unsafe {
            let tracked parent_record = resources.tracked_borrow_record_mut(parent_paddr);
            proof {
                assert(parent_record.node.inv());
                assert(regions.inv());
                assert(regions.slot_owners.contains_key(parent_record.node.slot_index));
                assert(regions.slots.contains_key(parent_record.node.slot_index));
                assert(regions.contains(parent_record.node.slot_index));
                parent_record.tracked_set_entry(
                    self.idx as int,
                    FlatEntryOwner::tracked_new_node(paddr, child_path, level),
                );
            }
            #[verus_spec(with Tracked(&mut parent_record.node), Tracked(&*regions))]
            self.node.write_pte(self.idx, self.pte);
            proof {
                assert(parent_record.local_inv());
                assert(parent_record.node.permission_matches(parent_permission));
            }
        };

        let tracked cursor_owner = FlatCursorOwner {
            resources,
            continuations,
            root,
            level: cursor_level,
            guard_level,
            va,
            prefix,
            barrier_va,
            popped_too_high,
        };
        proof {
            reveal(crate::specs::mm::page_table::FlatCursorResources::inv);
            assert(*cursor_owner.resources.root.record == root_record_before_publish);
            assert forall|key: Paddr| #[trigger] cursor_owner.resources.leases.contains_key(key) implies {
                let lease = cursor_owner.resources.leases[key];
                &&& lease.paddr == key
                &&& lease.record.paddr() == key
                &&& lease.record.local_inv()
                &&& lease.permission.frac() == 1
                &&& lease.record.node.permission_matches(*lease.permission)
            } by {
                if key != paddr && key != parent_paddr {
                    assert(original_owner.resources.contains_raw_leased(key));
                    assert(cursor_owner.resources.leased_record(key)
                        == original_owner.resources.leased_record(key));
                    assert(original_owner.resources.inv());
                }
            };
            assert(cursor_owner.resources.inv());
            assert(original_owner.as_page_table_owner().leaf_node_insert(
                cursor_owner.as_page_table_owner(), parent_paddr, self.idx as int, paddr));
            let before = original_owner.as_page_table_owner();
            let after = cursor_owner.as_page_table_owner();
            assert forall|key: Paddr| #[trigger] after.contains_node(key) implies after.local_node_inv(key) by {
                assert(after.node(key).local_inv());
                if key != paddr {
                    assert(before.contains_node(key));
                    before.lemma_node_inv(key);
                }
                assert forall|i: int| 0 <= i < NR_ENTRIES
                    && (#[trigger] after.node(key).entries[i]).is_node() implies {
                    let entry = after.node(key).entries[i];
                    &&& after.contains_node(entry.child_paddr())
                    &&& after.raw_node_permissions.contains_key(entry.child_paddr())
                    &&& after.node(entry.child_paddr()).path == entry.path
                    &&& after.node(entry.child_paddr()).node.level + 1 == after.node(key).node.level
                } by {
                    if key != parent_paddr || i != self.idx {
                        assert(key != paddr);
                        assert(before.node(key).entries[i].is_node());
                        assert(after.node(key).entries[i] == before.node(key).entries[i]);
                    }
                };
            };
            assert(after.raw_node_permissions.dom() == after.nodes.dom().remove(after.root));
            assert forall|key: Paddr| #[trigger] after.raw_node_permissions.contains_key(key) implies {
                &&& after.raw_node_permissions[key].frac() == 1
                &&& after.node(key).node.permission_matches(after.raw_node_permissions[key])
            } by {
                if cursor_owner.resources.leases.contains_key(key) {
                    assert(cursor_owner.resources.contains_raw_leased(key));
                } else {
                    assert(cursor_owner.resources.remainder.permissions.contains_key(key));
                }
            };
            before.lemma_leaf_node_insert_inv(after, parent_paddr, self.idx as int, paddr);
            assert(cursor_owner.continuations == original_owner.continuations);
            assert(cursor_owner.level == original_owner.level);
            assert forall|key: int| #[trigger] cursor_owner.continuations.contains_key(key)
                implies cursor_owner.continuation_inv(key) by {
                assert(original_owner.continuation_inv(key));
                let cont = cursor_owner.continuations[key];
                assert(cursor_owner.resources.contains_leased(cont.node));
                assert(cursor_owner.resources.leased_record(cont.node).path == cont.path);
                assert(cursor_owner.resources.leased_record(cont.node).node.level == cont.level);
                assert(cursor_owner.resources.leased_record(cont.node).node.relate_guard(cont.guard));
                if cont.node != cursor_owner.root {
                    assert(cursor_owner.resources.contains_raw_leased(cont.node));
                    assert(**cont.guard.inner.tracked_metadata_perm
                        == *cursor_owner.resources.leases[cont.node].permission);
                }
            };
            assert forall|key: int| #[trigger] cursor_owner.continuations.contains_key(key)
                && key < cursor_owner.guard_level - 1 implies {
                let child = cursor_owner.continuations[key];
                let parent = cursor_owner.continuations[key + 1];
                let record = cursor_owner.resources.leased_record(parent.node);
                &&& child.path == parent.path.push_tail(parent.idx as int)
                &&& record.entries[parent.idx as int].is_node()
                &&& record.entries[parent.idx as int].child_paddr() == child.node
            } by {
                let parent = cursor_owner.continuations[key + 1];
                assert(original_owner.continuations.contains_key(key + 1));
                assert(original_owner.continuation_inv(key + 1));
                assert(parent.node != parent_paddr);
                assert(after.node(parent.node).entries == before.node(parent.node).entries);
            };
            assert(cursor_owner.inv());
            before.lemma_metaregion_fresh_slot_preserved(regions_before_alloc, *regions, paddr);
            crate::specs::mm::page_table::node::owners::lemma_count_present_upto_update(
                before.node(parent_paddr).node.children_perm.value(), NR_ENTRIES as int,
                self.idx as int, self.pte);
            assert(after.node(parent_paddr).node.count_consistent());
            assert forall|key: Paddr| #[trigger] after.contains_node(key) implies {
                let record = after.node(key);
                let idx = record.node.slot_index;
                &&& regions.ref_count(idx) != REF_COUNT_UNUSED
                &&& 0 < regions.ref_count(idx) <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].slot_vaddr == record.node.slot_vaddr()
                &&& regions.slots[idx].value().wf(regions.slot_owners[idx])
                &&& regions.slot_owners[idx].paths_in_pt == set![record.path]
                &&& record.node.metaregion_sound_node(*regions)
            } by {
                if key != paddr {
                    assert(before.contains_node(key));
                    assert(before.nodes_metaregion_sound(*regions));
                }
            };
            assert forall|key: Paddr| #[trigger] after.raw_node_permissions.contains_key(key) implies
                after.contains_node(key) && after.node(key).node.metaregion_sound(
                    after.raw_node_permissions[key], *regions) by {
                if key != paddr {
                    assert(before.raw_node_permissions.contains_key(key));
                    assert(before.raw_nodes_metaregion_sound(*regions));
                }
            };
            assert forall|key: Paddr, i: int| after.contains_node(key) && 0 <= i < NR_ENTRIES
                implies #[trigger] after.node(key).entries[i].metaregion_sound(*regions) by {
                if key == paddr {
                    let current = after.node(key).entries[i];
                    assert(current == initialized_entries[i]);
                    assert(current.metaregion_sound(regions_before_publish));
                    C::lemma_none_perm_well_formed(current.frame().mapped_pa, *regions);
                    assert(frame_to_index(current.frame().mapped_pa) != frame_to_index(paddr));
                    C::lemma_perm_well_formed_with_region_preserved(
                        current.frame().mapped_pa, Tracked(current.frame_permission()),
                        regions_before_publish, *regions);
                } else if key != parent_paddr || i != self.idx {
                    assert(before.contains_node(key));
                    assert(after.node(key).entries[i] == before.node(key).entries[i]);
                    assert(before.entries_metaregion_sound(*regions));
                }
            };
        }
        proof {
            let before = original_owner.as_page_table_owner();
            let after = cursor_owner.as_page_table_owner();
            before.lemma_huge_leaf_insert_mappings(after, parent_paddr, self.idx as int, paddr);
            if original_owner.in_locked_range() {
                original_owner.lemma_view_inv();
                original_owner.lemma_current_frame_present();
                let entry = original_owner.current_entry();
                let size = page_size::<C>((original_owner.level - 1) as PagingLevel);
                crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_next::<C>(
                    (original_owner.level - 1) as PagingLevel);
                original_owner.view().lemma_query_mapping();
                assert(entry.leaf_mappings() == set![original_owner.view().query_mapping()]);
                vstd::set::lemma_set_choose_len(entry.leaf_mappings());
                assert(entry.leaf_mappings().choose() == original_owner.view().query_mapping());
                assert(page_size::<C>(original_owner.level) / size == NR_ENTRIES) by (nonlinear_arith)
                    requires page_size::<C>(original_owner.level) == size * NR_ENTRIES, size > 0;
                assert(cursor_owner.view().mappings == original_owner.view().split_if_mapped_huge_spec(size).mappings);
            }
        }
        #[verus_spec(with |= Tracked(cursor_owner))]
        Some(pt_lock_guard)
    }

    /// Create a new entry at the node with guard.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety**: The caller must provide the owner of the entry and the parent node, and the entry
    /// must match the parent node's PTE at the given index.
    /// - **Safety**: The caller must provide a valid guard permission matching `guard`, and it must be guarding the
    /// correct parent.
    /// ## Postconditions
    /// - **Correctness**: The resulting entry matches the owner.
    /// ## Safety
    /// - The precondition ensures that the index is within the bounds of the node.
    /// - This function does not modify the actual entry or any other relevant structure, so it is safe to call.
    /// Because we also require the guard to be correct, it will be safe to use the resulting `Entry` as a handle to the
    /// underlying `PTE`.
    #[verus_spec(res =>
        with Ghost(owner): Ghost<EntryOwner<C>>,
             Tracked(parent_owner): Tracked<&NodeOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            owner.inv(),
            parent_owner.inv(),
            parent_owner.relate_guard(*guard),
            idx < NR_ENTRIES,
            owner.match_pte(parent_owner.children_perm.value()[idx as int], owner.parent_level),
            regions.inv(),
            regions.slots.contains_key(parent_owner.slot_index),
        ensures
            res.wf(owner),
            res.idx == idx,
            parent_owner.relate_guard(*res.node),
            res.pte == parent_owner.children_perm.value()[idx as int],
            // Pinpoint the reborrow: the Entry's node is exactly the guard
            // we were handed in, so callers get `*res.node == *old(guard)`.
            *res.node == *old(guard),
            *final(guard) == *final(res.node),
    )]
    pub(in crate::mm) unsafe fn new_at(guard: &'a mut PageTableGuard<'rcu, C>, idx: usize) -> Self {
        // SAFETY: The index is within the bound.
        let pte = unsafe {
            #[verus_spec(with Tracked(parent_owner), Tracked(regions))]
            guard.read_pte(idx)
        };
        Self::new(pte, idx, guard)
    }
}

#[verus_verify]
impl<'rcu, C: PageTableConfig> PageTableGuard<'rcu, C> {
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut FlatEntryOwner<C>>,
             Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            old(owner).inv(),
            old(owner).is_frame(),
            old(owner).match_pte(
                old(parent_owner).children_perm.value()[idx as int],
            ),
            old(parent_owner).inv(),
            old(parent_owner).relate_guard(*old(self)),
            old(parent_owner).level() == old(owner).parent_level,
            old(parent_owner).metaregion_sound_node(*regions),
            idx < NR_ENTRIES,
            op.requires((old(owner).frame().prop,)),
            regions.inv(),
            regions.slots.contains_key(old(parent_owner).slot_index),
            forall|pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty,
                perm: Tracked<Option<C::Perm>>|
                #![auto]
                op.ensures((p_in,), p_out) ==> (
                    C::item_into_raw(C::item_from_raw(pa, level, p_out, perm)).3@
                        is Some
                ) == (perm@ is Some),
            forall|pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty|
                #![auto]
                op.ensures((p_in,), p_out) && C::E::new_page_req(pa, level, p_in)
                    ==> C::E::new_page_req(pa, level, p_out),
        ensures
            final(owner).inv(),
            final(owner).is_frame(),
            final(owner).match_pte(res),
            final(owner).match_pte(
                final(parent_owner).children_perm.value()[idx as int],
            ),
            res == final(parent_owner).children_perm.value()[idx as int],
            final(parent_owner).inv(),
            final(parent_owner).slot_index == old(parent_owner).slot_index,
            final(parent_owner).level() == old(parent_owner).level(),
            final(parent_owner).tree_level == old(parent_owner).tree_level,
            final(parent_owner).meta_own.nr_children.id() == old(parent_owner).meta_own.nr_children.id(),
            final(parent_owner).meta_own.stray == old(parent_owner).meta_own.stray,
            final(parent_owner).relate_guard(*final(self)),
            final(parent_owner).metaregion_sound_node(*regions),
            final(owner).frame().mapped_pa == old(owner).frame().mapped_pa,
            final(owner).frame_permission() == old(owner).frame_permission(),
            final(owner).frame_is_tracked() == old(owner).frame_is_tracked(),
            final(owner).path == old(owner).path,
            final(owner).parent_level == old(owner).parent_level,
            forall|j: int| 0 <= j < NR_ENTRIES && j != idx ==>
                #[trigger] final(parent_owner).children_perm.value()[j]
                    == old(parent_owner).children_perm.value()[j],
            crate::specs::mm::page_table::node::owners::count_present(
                final(parent_owner).children_perm.value(),
            ) == crate::specs::mm::page_table::node::owners::count_present(
                old(parent_owner).children_perm.value(),
            ),
            op.ensures((old(owner).frame().prop,), final(owner).frame().prop),
            *final(self) == *old(self),
    )]
    pub(in crate::mm) fn protect_child(
        &mut self,
        idx: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> C::E {
        let ghost cp_old = parent_owner.children_perm.value();
        let mut pte = unsafe {
            #[verus_spec(with Tracked(&*parent_owner), Tracked(regions))]
            self.read_pte(idx)
        };

        let prop = pte.prop();
        let new_prop = op(prop);

        proof {
            assert(owner.frame().prop == prop);
            assert(op.ensures((prop,), new_prop));
            C::lemma_raw_item_well_formed_preserved(
                owner.frame().mapped_pa,
                owner.parent_level,
                prop,
                new_prop,
                Tracked(owner.frame_permission()),
            );
        }

        assume(pte.set_prop_req(new_prop));
        pte.set_prop(new_prop);

        unsafe {
            #[verus_spec(with Tracked(parent_owner), Tracked(regions))]
            self.write_pte(idx, pte)
        };

        proof {
            owner.tracked_set_frame_prop(new_prop);
            // The PTE at `idx` stayed present (only `prop` changed), so the
            // present-count is unchanged by the `write_pte` update — preserving
            // `count_consistent` for the caller.
            crate::specs::mm::page_table::node::owners::lemma_count_present_upto_update(
                cp_old,
                NR_ENTRIES as int,
                idx as int,
                pte,
            );
        }

        pte
    }

    #[verifier::spinoff_prover]
    #[verus_spec(res =>
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
             Tracked(owner): Tracked<&mut EntryOwner<C>>,
             Tracked(new_owner): Tracked<&mut EntryOwner<C>>,
             Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
        requires
            old(owner).inv(),
            old(owner).metaregion_sound(*old(regions)),
            old(owner).match_pte(
                old(parent_owner).children_perm.value()[idx as int],
                old(owner).parent_level,
            ),
            old(parent_owner).inv(),
            old(parent_owner).relate_guard(*old(self)),
            old(parent_owner).level() == old(owner).parent_level,
            idx < NR_ENTRIES,
            old(regions).inv(),
            old(regions).slots.contains_key(old(parent_owner).slot_index),
            new_child.invariants(*old(new_owner), *old(regions)),
            old(owner).path == old(new_owner).path,
            old(owner).parent_level == old(new_owner).parent_level,
            old(new_owner).is_node() ==> {
                &&& old(regions).slots.contains_key(frame_to_index(old(new_owner).meta_slot_paddr()->0))
                &&& old(regions).slot_owner(old(new_owner).meta_slot_paddr()->0).ref_count() != REF_COUNT_UNUSED
            },
            old(parent_owner).metaregion_sound_node(*old(regions)),
        ensures
            res.invariants(*final(owner), *final(regions)),
            final(new_owner).inv(),
            final(new_owner).metaregion_sound(*final(regions)),
            final(new_owner).match_pte(
                final(parent_owner).children_perm.value()[idx as int],
                final(parent_owner).level(),
            ),
            final(new_owner).path == old(new_owner).path,
            final(new_owner).parent_level == old(new_owner).parent_level,
            *final(owner) == old(owner).from_pte_owner_spec(),
            *final(new_owner) == old(new_owner).into_pte_owner_spec(),
            Entry::<C>::metaregion_sound_neq_preserved(
                *old(owner),
                *final(new_owner),
                *old(regions),
                *final(regions),
            ),
            !final(new_owner).is_node() ==> Entry::<C>::metaregion_sound_neq_old_preserved(
                *old(owner),
                *old(regions),
                *final(regions),
            ),
            (!old(owner).is_node() && !final(new_owner).is_node())
                ==> Entry::<C>::metaregion_sound_preserved(*old(regions), *final(regions)),
            final(new_owner).is_node() && !final(new_owner).is_absent() ==> PageTableOwner::<
                C,
            >::path_tracked_pred(*final(regions))(*final(new_owner), final(new_owner).path),
            final(parent_owner).inv(),
            final(parent_owner).level() == old(parent_owner).level(),
            final(parent_owner).relate_guard(*final(self)),
            final(parent_owner).metaregion_sound_node(*final(regions)),
            forall|j: int| 0 <= j < NR_ENTRIES && j != idx ==>
                #[trigger] final(parent_owner).children_perm.value()[j]
                    == old(parent_owner).children_perm.value()[j],
            forall|slot: int|
                #![trigger final(regions).slot_owners[slot].paths_in_pt]
                (!final(new_owner).is_node() || final(new_owner).is_absent() || slot
                    != frame_to_index(final(new_owner).meta_slot_paddr()->0))
                    ==> final(regions).slot_owners[slot].paths_in_pt == old(
                    regions,
                ).slot_owners[slot].paths_in_pt,
            forall|slot: int|
                #![trigger final(regions).slot_owners[slot].ref_count()]
                final(regions).ref_count(slot) == old(
                    regions,
                ).ref_count(slot),
            forall|slot: int|
                #![trigger final(regions).slot_owners[slot].ref_count_perm]
                final(regions).slot_owners[slot].same_permissions(
                    old(regions).slot_owners[slot],
                ),
            final(regions).slots == old(regions).slots,
            (!old(owner).is_node() && !final(new_owner).is_node()) ==> {
                &&& forall|i: int|
                    #![trigger final(regions).slot_owners[i]]
                    final(regions).slot_owners[i] == old(
                        regions,
                    ).slot_owners[i]
            },
            Entry::<C>::replace_nonpanic_condition(*old(parent_owner), *old(new_owner)),
            *final(self) == *old(self),
    )]
    #[verifier::spinoff_prover]
    pub(in crate::mm) fn replace_child(&mut self, idx: usize, new_child: Child<C>) -> Child<C> {
        let ghost initial_regions = *regions;
        let ghost initial_owner = *owner;
        let ghost initial_new_owner = *new_owner;
        #[cfg(feature = "allow_panic")]
        {
            let guard_level = self.level();
            match &new_child {
                Child::PageTable(node) => {
                    assert!(node.level() == guard_level - 1);
                },
                Child::Frame(_, level, _) => {
                    assert!(*level == guard_level);
                },
                Child::None => {},
            }
        }

        let pte = unsafe {
            #[verus_spec(with Tracked(&*parent_owner), Tracked(&*regions))]
            self.read_pte(idx)
        };

        #[verus_spec(with Tracked(Some(
            (*self.inner.tracked_metadata_perm.borrow()).tracked_borrow(),
        )))]
        let level = self.level();

        let old_child = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(owner))]
            Child::from_pte(pte, level)
        };

        // For restoring `count_consistent` after the PTE swap below.
        let ghost cp0 = parent_owner.children_perm.value();

        if old_child.is_none() && !new_child.is_none() {
            #[verus_spec(with
                Tracked(NodeOwner::<C>::tracked_borrow_frame_metadata_perm(
                    *self.inner.tracked_metadata_perm.borrow(),
                )),
                Ghost(parent_owner.meta_own.nr_children.id())
            )]
            let nr_children = self.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            proof {
                parent_owner.nr_children_absent_slot_bound(idx);
            }
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            #[verus_spec(with
                Tracked(NodeOwner::<C>::tracked_borrow_frame_metadata_perm(
                    *self.inner.tracked_metadata_perm.borrow(),
                )),
                Ghost(parent_owner.meta_own.nr_children.id())
            )]
            let nr_children = self.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            proof {
                parent_owner.nr_children_present_slot_bound(idx);
            }
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp - 1);
        }
        #[verus_spec(with Tracked(new_owner))]
        let new_pte = new_child.into_pte();

        unsafe {
            #[verus_spec(with Tracked(parent_owner), Tracked(&*regions))]
            self.write_pte(idx, new_pte)
        };

        proof {
            crate::specs::mm::page_table::node::owners::lemma_count_present_upto_update(
                cp0,
                NR_ENTRIES as int,
                idx as int,
                new_pte,
            );
        }

        proof {
            if new_owner.is_node() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.lemma_contains_valid_frame_paddr(paddr);
                let tracked mut new_meta_slot = regions.tracked_borrow_mut_slot_owner(paddr);
                new_meta_slot.paths_in_pt = set![new_owner.path];
            }
        }

        proof {
            if new_owner.is_node() || new_owner.is_frame() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.lemma_contains_valid_frame_paddr(paddr);
            }
            if owner.is_frame() {
                let paddr = owner.frame().mapped_pa;
                let slot = frame_to_index(paddr);
                assert(initial_regions.slots[slot] == regions.slots[slot]);
                assert(initial_regions.slot_owners[slot].metadata_perm.id()
                    == regions.slot_owners[slot].metadata_perm.id());
                C::lemma_perm_well_formed_with_region_preserved(
                    paddr,
                    Tracked(owner.frame_permission()),
                    initial_regions,
                    *regions,
                );
            }
            if new_owner.is_frame() {
                let paddr = new_owner.frame().mapped_pa;
                let slot = frame_to_index(paddr);
                assert(initial_regions.slots[slot] == regions.slots[slot]);
                assert(initial_regions.slot_owners[slot].metadata_perm.id()
                    == regions.slot_owners[slot].metadata_perm.id());
                C::lemma_perm_well_formed_with_region_preserved(
                    paddr,
                    Tracked(new_owner.frame_permission()),
                    initial_regions,
                    *regions,
                );
            }
            assert(Entry::<C>::metaregion_sound_neq_preserved(
                initial_owner,
                *new_owner,
                initial_regions,
                *regions,
            )) by {
                let f = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.meta_slot_paddr_neq(initial_owner) && entry.meta_slot_paddr_neq(
                        *new_owner,
                    ) && entry.metaregion_sound(initial_regions);
                let g = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.metaregion_sound(*regions);
                assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                    if entry.is_frame() {
                        let paddr = entry.frame().mapped_pa;
                        let slot = frame_to_index(paddr);
                        assert(initial_regions.slots[slot] == regions.slots[slot]);
                        assert(initial_regions.slot_owners[slot].metadata_perm.id()
                            == regions.slot_owners[slot].metadata_perm.id());
                        C::lemma_perm_well_formed_with_region_preserved(
                            paddr,
                            Tracked(entry.frame_permission()),
                            initial_regions,
                            *regions,
                        );
                    }
                };
            };
        }

        old_child
    }

    #[verifier::spinoff_prover]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(owner): Tracked<&mut FlatEntryOwner<C>>,
             Tracked(parent_owner): Tracked<&mut FlatNodeOwner<C>>,
        requires
            old(owner).inv(),
            old(owner).is_absent(),
            old(parent_owner).inv(),
            old(parent_owner).relate_guard(*old(self)),
            old(parent_owner).level == old(owner).parent_level,
            idx < NR_ENTRIES,
            old(owner).match_pte(
                old(parent_owner).children_perm.value()[idx as int],
            ),
            old(regions).inv(),
            old(regions).slots.contains_key(old(parent_owner).slot_index),
            old(parent_owner).metaregion_sound(
                **old(self).inner.tracked_metadata_perm,
                *old(regions),
            ),
            level == old(owner).parent_level,
            FlatEntryOwner::<C>::new_frame(paddr, old(owner).path, level, prop, None).inv(),
            C::E::new_page_req(paddr, level, prop),
            C::raw_item_well_formed((paddr, level, prop, Tracked(None))),
        ensures
            final(parent_owner).inv(),
            final(parent_owner).count_consistent(),
            *final(owner) == FlatEntryOwner::new_frame(
                paddr,
                old(owner).path,
                level,
                prop,
                None,
            ),
            final(owner).match_pte(final(parent_owner).children_perm.value()[idx as int]),
            forall|i: int|
                0 <= i < NR_ENTRIES && i != idx ==> #[trigger] old(parent_owner).children_perm.value()[i]
                    == final(parent_owner).children_perm.value()[i],
            final(parent_owner).slot_index == old(parent_owner).slot_index,
            final(parent_owner).level == old(parent_owner).level,
            final(parent_owner).tree_level == old(parent_owner).tree_level,
            final(parent_owner).meta_own.nr_children.id() == old(parent_owner).meta_own.nr_children.id(),
            final(parent_owner).meta_own.stray == old(parent_owner).meta_own.stray,
            final(parent_owner).relate_guard(*final(self)),
            final(parent_owner).metaregion_sound(
                **final(self).inner.tracked_metadata_perm,
                *final(regions),
            ),
            *final(regions) == *old(regions),
            *final(self) == *old(self),
    )]
    pub(in crate::mm) fn replace_absent_with_frame(
        &mut self,
        idx: usize,
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) {
        proof {
            C::lemma_paging_consts_properties();
        }
        // For restoring `count_consistent` after the absent→frame install.
        let ghost cp0 = parent_owner.children_perm.value();
        let tracked node_metadata_perm = (
        *self.inner.tracked_metadata_perm.borrow()).tracked_borrow();
        #[verus_spec(with Tracked(node_metadata_perm),
            Ghost(parent_owner.meta_own.nr_children.id()))]
        let nr_children = self.nr_children_mut();
        let old_nr_children = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
        proof {
            parent_owner.nr_children_absent_slot_bound(idx);
        }
        nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), old_nr_children + 1);

        let tracked mut pte_owner = EntryOwner::tracked_new_frame(
            paddr,
            owner.path,
            level,
            prop,
            None,
        );
        #[verus_spec(with Tracked(&mut pte_owner))]
        let new_pte = Child::<C>::Frame(paddr, level, prop).into_pte();

        unsafe {
            #[verus_spec(with Tracked(parent_owner), Tracked(&*regions))]
            self.write_pte(idx, new_pte)
        };

        proof {
            *owner = FlatEntryOwner::tracked_new_frame(paddr, owner.path, level, prop, None);
            // Restore the parent's `count_consistent`: slot `idx` went
            // absent → present (the new frame) and `nr_children` was
            // incremented by 1.
            crate::specs::mm::page_table::node::owners::lemma_count_present_upto_update(
                cp0,
                NR_ENTRIES as int,
                idx as int,
                new_pte,
            );
        }
    }
}

} // verus!
