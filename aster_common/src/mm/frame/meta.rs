mod mapping;
pub use mapping::*;

use vstd::atomic::PAtomicU8;
use vstd::atomic::PAtomicU64;
use vstd::cell::{self, PCell};
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};
use vstd_extra::ownership::*;
use vstd_extra::cast_ptr::*;

use core::ops::Deref;
use std::marker::PhantomData;
use super::*;

verus! {

/// The error type for getting the frame from a physical address.
#[derive(Debug)]
pub enum GetFrameError {
    /// The frame is in use.
    InUse,
    /// The frame is not in use.
    Unused,
    /// The frame is being initialized or destructed.
    Busy,
    /// The frame is private to an owner of [`UniqueFrame`].
    ///
    /// [`UniqueFrame`]: super::unique::UniqueFrame
    Unique,
    /// The provided physical address is out of bound.
    OutOfBound,
    /// The provided physical address is not aligned.
    NotAligned,
    /// Verification only: `compare_exchange` returned `Err`, retry
    Retry,
}

pub open spec fn get_slot_spec(paddr: Paddr) -> (res: PPtr<MetaSlot>)
    recommends
        paddr % 4096 == 0,
        paddr < MAX_PADDR(),
{
    let slot = frame_to_meta(paddr);
    PPtr(slot, PhantomData::<MetaSlot>)
}

pub struct StoredPageTablePageMeta {
    pub nr_children: PCell<u16>,
    pub stray: PCell<bool>,
    pub level: PagingLevel,
    pub lock: PAtomicU8,
}

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    FrameLink(StoredLink),
    PTNode(StoredPageTablePageMeta),
}

impl MetaSlotStorage {
    pub open spec fn get_link_spec(self) -> Option<StoredLink> {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None
        }
    }

    #[verifier::when_used_as_spec(get_link_spec)]
    pub fn get_link(self) -> (res: Option<StoredLink>)
        ensures res == self.get_link_spec()
    {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None
        }
    }

    pub open spec fn get_node_spec(self) -> Option<StoredPageTablePageMeta> {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None
        }
    }

    #[verifier::when_used_as_spec(get_node_spec)]
    pub fn get_node(self) -> (res: Option<StoredPageTablePageMeta>)
        ensures res == self.get_node_spec()
    {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None
        }
    }
}

#[rustc_has_incoherent_inherent_impls]
pub struct MetaSlot {
    pub storage: PPtr<MetaSlotStorage>,
    pub ref_count: PAtomicU64,
    pub vtable_ptr: PPtr<usize>,
    pub in_list: PAtomicU64,
}

//global layout MetaSlot is size == 64, align == 8;

pub broadcast proof fn lemma_meta_slot_size()
    ensures
        #[trigger] size_of::<MetaSlot>() == META_SLOT_SIZE(),
{ admit() }

pub proof fn size_of_meta_slot()
    ensures
        size_of::<MetaSlot>() == 64,
        align_of::<MetaSlot>() == 8,
{ admit() }

#[inline(always)]
#[verifier::allow_in_spec]
pub const fn meta_slot_size() -> (res: usize)
    returns
        64usize,
{
    proof { size_of_meta_slot(); }
    size_of::<MetaSlot>()
}

impl MetaSlot {
    pub fn cast_storage<T: Repr<MetaSlotStorage>>(&self, addr: usize, Tracked(owner): Tracked<&MetaSlotOwner>) -> (res: ReprPtr<MetaSlotStorage, T>)
        requires
            self.wf(owner),
            owner.inv(),
            addr == owner.storage@.addr()
        ensures
            res.ptr == owner.storage@.pptr(),
            res.addr == addr
    {
        ReprPtr::<MetaSlotStorage, T> {
            addr: addr,
            ptr: self.storage,
            _T: PhantomData
        }
    }

    pub open spec fn get_from_unused_spec<M: AnyFrameMeta>
    (
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionModel,
    ) -> (PPtr<MetaSlot>, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.slots[frame_to_index(paddr)].ref_count == REF_COUNT_UNUSED,
    {
        let ptr = get_slot_spec(paddr);
        let idx = frame_to_index(paddr);
        let (rc, status) = if as_unique_ptr {
            (REF_COUNT_UNIQUE, MetaSlotStatus::UNIQUE)
        } else {
            (1, MetaSlotStatus::SHARED)
        };
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx,
                MetaSlotModel {
                    status,
                    storage: cell::MemContents::Init(metadata.to_repr()),
                    ref_count: rc,
                    vtable_ptr: simple_pptr::MemContents::Init(metadata.vtable_ptr()),
                    in_list: 0,
                    self_addr: ptr.addr(),
                    usage: PageUsage::Frame,
                },
            ),
        };
        (ptr, post)
    }


    /*    pub open spec fn get_from_in_use_owner_spec<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionOwners,
    ) -> MetaRegionOwners
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
    {
        let ptr = get_slot_spec(paddr);
        let idx = frame_to_index(paddr);
        let (rc, status) = if as_unique_ptr {
            (REF_COUNT_UNIQUE, MetaSlotStatus::UNIQUE)
        } else {
            (1, MetaSlotStatus::SHARED)
        };
        MetaRegionModel {
            slot_owners: pre.slots.insert(
                idx, MetaSlotOwner {
                    status,
                    storage: cell::MemContents::Init(metadata.write_as()),
                    ref_count: rc,
                    vtable_ptr: simple_pptr::MemContents::Init(metadata.vtable_ptr()),
                    in_list: 0,
                    self_addr: ptr.addr(),
                    usage: PageUsage::Frame,
                }
            )
        }
    }*/
    /// All other slots remain unchanged.
    pub open spec fn update_index_tracked(
        idx: usize,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            pre.slots.contains_key(idx),
    {
        &&& pre.slots.dom() == post.slots.dom()
        &&& pre.dropped_slots.dom() == post.dropped_slots.dom()
        &&& pre.slot_owners.dom() == post.slot_owners.dom()
        &&& forall|i: usize| #[trigger]
            pre.slots.contains_key(i) && i != idx ==> pre.slots[i] == post.slots[i]
        &&& forall|i: usize| #[trigger]
            pre.dropped_slots.contains_key(i) && i != idx ==> pre.dropped_slots[i]
                == post.dropped_slots[i]
        &&& forall|i: usize| #[trigger]
            pre.slot_owners.contains_key(i) && i != idx ==> pre.slot_owners[i]
                == post.slot_owners[i]
    }

    pub open spec fn get_from_unused_tracked<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.view().slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let idx = paddr / 4096;
        {
            &&& Self::update_index_tracked(idx, pre, post)
            &&& Self::get_from_unused_spec(paddr, metadata, as_unique_ptr, pre.view()).1
                == post.view()
        }
    }

    pub open spec fn get_from_in_use_spec(paddr: Paddr, pre: MetaRegionModel) -> (
        PPtr<MetaSlot>,
        MetaRegionModel,
    )
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            0 <= pre.slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let ptr = get_slot_spec(paddr);
        let idx = paddr / 4096;
        let pre_slot = pre.slots[idx];
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx,
                MetaSlotModel { ref_count: (pre_slot.ref_count + 1) as u64, ..pre_slot },
            ),
        };
        (ptr, post)
    }

    pub open spec fn get_from_in_use_tracked(
        paddr: Paddr,
        // -- ghost parameters --
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            0 <= pre.view().slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let idx = paddr / 4096;
        {
            &&& Self::update_index_tracked(idx, pre, post)
            &&& Self::get_from_in_use_spec(paddr, pre.view()).1 == post.view()
        }
    }

    pub open spec fn inc_ref_count_spec(&self, pre: MetaSlotModel) -> (MetaSlotModel)
        recommends
            pre.inv(),
            pre.status == MetaSlotStatus::SHARED,
    {
        MetaSlotModel { ref_count: (pre.ref_count + 1) as u64, ..pre }
    }

    pub open spec fn frame_paddr_spec(&self, pre: MetaSlotModel) -> Paddr {
        mapping::meta_to_frame_spec(pre.self_addr)
    }
}

/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta: Repr<MetaSlotStorage> {
    exec fn on_drop(&mut self) {}

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;
}


}