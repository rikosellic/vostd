use vstd::prelude::*;
use vstd::simple_pptr::{self, *};
use vstd::cell;
use vstd::atomic::*;

use std::marker::PhantomData;
use std::ops::Range;

use crate::mm::*;

use crate::prelude::PageTablePageMetaInner;
use crate::prelude::PageUsage;

verus! {

pub trait Inv {
    spec fn inv(&self) -> bool;
}

pub trait InvView: Inv {
    type V: Inv;

    spec fn view(&self) -> Self::V
        recommends self.inv();

    proof fn view_preserves_inv(&self)
        requires self.inv(),
        ensures self.view().inv(),
    ;
}


pub trait OwnerOf {
    /// The owner of the concrete type.
    /// The Owner must implement `Inv`, indicating that it must
    /// has a consistent state.
    type Owner: InvView;

    spec fn wf(&self, owner: &Self::Owner) -> bool
        recommends owner.inv(),
    ;
}

pub trait ModelOf: OwnerOf {
    open spec fn model(&self, owner: &Self::Owner) -> <Self::Owner as InvView>::V
        recommends
            self.wf(owner),
    {
        owner.view()
    }
}

/*


pub open spec fn get_slot_spec(paddr: Paddr) -> (res: PPtr<MetaSlot>)
    recommends
        paddr % 4096 == 0,
        paddr < frame::MAX_PADDR,
{
    let slot = mapping::frame_to_meta(paddr);
    PPtr(slot, PhantomData::<MetaSlot>)
}


/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta {
    exec fn on_drop(&mut self) {}

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;

    spec fn cast_to(x: &MetaSlotStorage) -> &Self;

    spec fn write_as(&self) -> MetaSlotStorage;
}


impl MetaSlot {

    pub open spec fn get_from_unused_spec<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionModel,
    ) -> (PPtr<MetaSlot>, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let ptr = get_slot_spec(paddr);
        let idx = paddr / 4096;
        let (rc, status) = if as_unique_ptr {
            (REF_COUNT_UNIQUE, MetaSlotStatus::UNIQUE)
        } else {
            (1, MetaSlotStatus::SHARED)
        };
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx, MetaSlotModel {
                    status,
                    storage: MemContents::Init(metadata.write_as()),
                    ref_count: rc,
                    vtable_ptr: MemContents::Init(metadata.vtable_ptr()),
                    in_list: 0,
                    self_addr: ptr.addr(),
                    usage: PageUsage::Frame,
                }
            )
        };
        (ptr, post)
    }

    /// All other slots remain unchanged.
    pub open spec fn update_index_tracked(idx: usize, pre: MetaRegionOwners, post: MetaRegionOwners)
        -> bool
        recommends
            pre.slots.contains_key(idx)
    {
    &&& pre.slots.dom() == post.slots.dom()
    &&& pre.slot_owners.dom() == post.slot_owners.dom()
    &&& forall |i: usize| #[trigger]
        pre.slots.contains_key(i) && i != idx ==>
            pre.slots[i] == post.slots[i]
    &&& forall |i: usize| #[trigger]
        pre.slot_owners.contains_key(i) && i != idx ==>
            pre.slot_owners[i] == post.slot_owners[i]
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
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.view().slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let idx = paddr / 4096;
        {
        &&& Self::update_index_tracked(idx, pre, post)
        &&& Self::get_from_unused_spec(paddr, metadata, as_unique_ptr, pre.view()).1 ==
            post.view()
        }
    }

    pub open spec fn get_from_in_use_spec(paddr: Paddr, pre: MetaRegionModel) 
        -> (PPtr<MetaSlot>, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            0 <= pre.slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let ptr = get_slot_spec(paddr);
        let idx = paddr / 4096;
        let pre_slot = pre.slots[idx];
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx, MetaSlotModel {
                    ref_count: (pre_slot.ref_count + 1) as u64,
                    ..pre_slot
                }
            )
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
            paddr < frame::MAX_PADDR,
            pre.inv(),
            0 <= pre.view().slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let idx = paddr / 4096;
        {
        &&& Self::update_index_tracked(idx, pre, post)
        &&& Self::get_from_in_use_spec(paddr, pre.view()).1 == post.view()
        }
    }

    pub open spec fn inc_ref_count_spec(&self, pre: MetaSlotModel)
        -> (MetaSlotModel)
        recommends
            pre.inv(),
            pre.status == MetaSlotStatus::SHARED,
    {
        MetaSlotModel {
            ref_count: (pre.ref_count + 1) as u64,
            ..pre
        }
    }

    pub open spec fn frame_paddr(&self, pre: MetaSlotModel) -> Paddr {
        mapping::meta_to_frame_spec(pre.self_addr)
    }
}


pub struct UniqueFrame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

pub tracked struct UniqueFrameOwner {
    pub slot: Tracked<MetaSlotOwner>,
}

pub ghost struct UniqueFrameModel {
    pub slot: MetaSlotModel,
}


impl Inv for UniqueFrameOwner {
    open spec fn inv(&self) -> bool {
    &&& self.slot@.inv()
    &&& self.slot@.ref_count@.value() == REF_COUNT_UNIQUE
    &&& self.slot@.vtable_ptr@.is_init()
    &&& self.slot@.storage@.is_init()
    }
}

impl Inv for UniqueFrameModel {
    open spec fn inv(&self) -> bool {
    &&& self.slot.inv()
    &&& self.slot.status == MetaSlotStatus::UNIQUE
    &&& self.slot.ref_count == REF_COUNT_UNIQUE
    &&& self.slot.vtable_ptr.is_init()
    &&& self.slot.storage.is_init()
    }
}

impl InvView for UniqueFrameOwner {
    type V = UniqueFrameModel;

    open spec fn view(&self) -> Self::V {
        UniqueFrameModel {
            slot: self.slot@.view(),
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl <M: AnyFrameMeta> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
    &&& self.ptr == owner.slot@.self_ptr@.pptr()
    }
}

impl <M: AnyFrameMeta> ModelOf for UniqueFrame<M> { }

impl <M: AnyFrameMeta> UniqueFrame<M> {

    pub open spec fn from_unused_spec(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        -> (Self, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let (ptr, post) = MetaSlot::get_from_unused_spec(paddr, metadata, true, pre);
        (UniqueFrame { ptr, _marker: PhantomData }, post)
    }


    pub proof fn from_unused_properties(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        requires
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
        ensures
            UniqueFrame::from_unused_spec(paddr, metadata, pre).1.inv(),
    { }

    pub open spec fn meta_spec(&self, pre: UniqueFrameModel) -> &M 
        recommends
            pre.inv(),
    {
        M::cast_to(&pre.slot.storage.value())
    }

    pub open spec fn replace_spec(&self, metadata: M, pre: UniqueFrameModel)
        -> UniqueFrameModel
        recommends
            pre.inv(),
    {
        let storage = MemContents::Init(metadata.write_as());
        UniqueFrameModel {
            slot: MetaSlotModel {
                storage,
                ..pre.slot
            }
        }
    }

}

*/

}

