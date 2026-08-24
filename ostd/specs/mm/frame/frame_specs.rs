use core::marker::PhantomData;

use vstd::prelude::*;
use vstd_extra::{cast_ptr::*, drop_tracking::TrackDrop, ownership::*};

use crate::specs::{
    arch::*,
    mm::frame::{
        mapping::{frame_to_index, meta_to_index},
        meta_owners::{FracMetadataPerm, PageUsage},
        meta_region_owners::MetaRegionOwners,
    },
};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        meta::{
            META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

verus! {

// Unbounded so `from_raw` (which lives in an unbounded `impl Frame<M>` block
// to break the AnyFrameMeta trait-resolution cycle in PT-node on_drop) can
// reference these helpers via `Self::from_raw_*`.
impl<'a, M: ?Sized> Frame<M> {
    /// The one-unit metadata permission carried by a shared frame or by its
    /// raw representation.
    pub open spec fn frame_permission_wf(
        regions: MetaRegionOwners,
        paddr: Paddr,
        permission: FracMetadataPerm,
    ) -> bool {
        let idx = frame_to_index(paddr);
        &&& regions.contains(idx)
        &&& permission.frac() == 1
        &&& permission.id() == regions.slot_owners[idx].metadata_perm.id()
        &&& permission.resource().storage_perm.id() == regions.slots[idx].value().storage.id()
        &&& permission.resource().storage_perm.is_init()
        &&& permission.resource().vtable_ptr_perm.pptr() == regions.slots[idx].value().vtable_ptr
        &&& permission.resource().vtable_ptr_perm.is_init()
    }

    // [`Frame::from_raw`] precondition
    pub open spec fn from_raw_requires_safety(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        &&& regions.slot_owner(paddr).slot_vaddr == frame_to_meta(paddr)
        &&& valid_frame_paddr(paddr)
        &&& regions.inv()
        &&& 0 < regions.slot_owner(paddr).ref_count() <= REF_COUNT_MAX
    }

    pub open spec fn from_raw_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        paddr: Paddr,
        r: Self,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_regions.contains(frame_to_index(paddr))
        &&& new_regions.slot_owner(paddr) =~= old_regions.slot_owner(paddr)
        &&& new_regions.slot_owner(paddr).slot_vaddr == r.ptr.addr()
        &&& forall|i: int|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != frame_to_index(paddr) ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& forall|i: int|
            i != frame_to_index(paddr) ==> new_regions.contains(i) == old_regions.contains(i)
        &&& r.ptr.addr() == frame_to_meta(paddr)
        &&& r.start_paddr_spec() == paddr
        &&& r.inv()
    }

    /// **Safety**: Frames other than this one are not affected by the call.
    pub open spec fn into_raw_post_noninterference(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    ) -> bool {
        &&& forall|i: int|
            #![trigger new_regions.slots[i], old_regions.slots[i]]
            i != self.index() && old_regions.contains(i) ==> new_regions.contains(i)
                && new_regions.slots[i] == old_regions.slots[i]
        &&& forall|i: int|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != self.index() ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& new_regions.slot_owners.dom() =~= old_regions.slot_owners.dom()
    }
}

impl<M: ?Sized> Inv for Frame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
    }
}

impl<M: ?Sized> Frame<M> {
    pub open spec fn index(self) -> int {
        frame_to_index(self.start_paddr_spec())
    }

    pub open spec fn start_paddr_spec(self) -> Paddr {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn from_unused_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let pre_owner = pre.slot_owner(paddr);
        let post_owner = post.slot_owner(paddr);
        {
            &&& pre_owner.ref_count() == REF_COUNT_UNUSED
            &&& MetaSlot::get_from_unused_owner_spec(false, post_owner)
            &&& post_owner.usage is Frame
            &&& post_owner.slot_vaddr == pre_owner.slot_vaddr
            &&& post_owner.paths_in_pt == pre_owner.paths_in_pt
            &&& post =~= pre.insert_slot_owner(paddr, post_owner)
        }
    }
}

impl<M: ?Sized> Frame<M> {
    /// Cross-object well-formedness predicate: this `Frame` handle and
    /// the supplied [`MetaRegionOwners`] state are mutually consistent.
    pub open spec fn wf_with_region(self, s: MetaRegionOwners) -> bool {
        let idx = self.index();
        let slot_own = s.slot_owners[idx];
        &&& self.inv()
        &&& s.inv()
        &&& s.contains(idx)
        &&& s.slots[idx].pptr() == self.ptr
        &&& 0 < slot_own.ref_count() <= REF_COUNT_MAX
        &&& self.tracked_perm@ is Some
        &&& self.tracked_perm@->0.frac() == 1
        &&& self.tracked_perm@->0.id() == slot_own.metadata_perm.id()
        &&& self.tracked_perm@->0.resource().storage_perm.id() == s.slots[idx].value().storage.id()
        &&& self.tracked_perm@->0.resource().storage_perm.is_init()
        &&& self.tracked_perm@->0.resource().vtable_ptr_perm.pptr()
            == s.slots[idx].value().vtable_ptr
        &&& self.tracked_perm@->0.resource().vtable_ptr_perm.is_init()
    }
}

impl<M: ?Sized> TrackDrop for Frame<M> {
    type State = MetaRegionOwners;

    type Obligation = ();

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        s1 == s0
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        ()
    }

    // It is unsound to drop a `Frame` while raw paddrs to it remain
    // outstanding (`raw_count > 0`), since those raw paddrs could be revived
    // via `from_raw`. Hence the drop is only permitted when `raw_count == 0`.
    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        let idx = self.index();
        let slot_own = s.slot_owners[idx];
        &&& self.wf_with_region(s)
        &&& slot_own.ref_count() == 1 ==> {
            &&& slot_own.paths_in_pt.is_empty()
        }
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        let idx = self.index();
        let so0 = s0.slot_owners[idx];
        let so1 = s1.slot_owners[idx];
        &&& s1.inv()
        &&& forall|i: int|
            #![trigger s1.slot_owners[i]]
            i != idx ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.slot_owners.dom()
            =~= s0.slot_owners.dom()
        &&& so1.slot_vaddr == so0.slot_vaddr
        &&& so1.usage == so0.usage
        &&& so1.paths_in_pt == so0.paths_in_pt
        &&& so1.metadata_perm.id() == so0.metadata_perm.id()
        &&& so0.ref_count() == 1 ==> so1.ref_count() == REF_COUNT_UNUSED
        &&& so0.ref_count() > 1 ==> so1.ref_count() == (so0.ref_count() - 1) as u64
    }
}

} // verus!
