use vstd::prelude::*;
use vstd::simple_pptr::{self, *};
use vstd::cell;
use vstd::atomic::*;

use vstd_extra::ownership::*;

use crate::prelude::*;

use std::marker::PhantomData;

verus! {

/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta {
    exec fn on_drop(&mut self) {}

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;

    spec fn cast_to_spec(x: &MetaSlotStorage) -> PPtr<Self> where Self: std::marker::Sized;

    exec fn cast_to(x: &MetaSlotStorage) -> PPtr<Self> where Self: std::marker::Sized;

    spec fn write_as_spec(&self) -> MetaSlotStorage;

    exec fn write_as(&self) -> MetaSlotStorage;
}

#[rustc_has_incoherent_inherent_impls]
pub struct UniqueFrame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta> {
    pub slot: Tracked<MetaSlotOwner>,
    pub perm: Tracked<PointsTo<M>>,
}

pub ghost struct UniqueFrameModel {
    pub slot: MetaSlotModel,
}

impl<M: AnyFrameMeta> Inv for UniqueFrameOwner<M> {
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

impl<M: AnyFrameMeta> InvView for UniqueFrameOwner<M> {
    type V = UniqueFrameModel;

    open spec fn view(&self) -> Self::V {
        UniqueFrameModel {
            slot: self.slot@.view(),
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl <M: AnyFrameMeta> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
    &&& self.ptr == owner.slot@.self_ptr@.pptr()
    }
}

impl <M: AnyFrameMeta> ModelOf for UniqueFrame<M> { }

impl <M: AnyFrameMeta> UniqueFrame<M> {

    pub open spec fn from_unused_spec(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        -> (Self, MetaRegionModel)
        recommends
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.slots[frame_to_index(paddr)].ref_count == REF_COUNT_UNUSED,
    {
        let (ptr, post) = MetaSlot::get_from_unused_spec(paddr, metadata, true, pre);
        (UniqueFrame { ptr, _marker: PhantomData }, post)
    }


    pub proof fn from_unused_properties(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        requires
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
        ensures
            UniqueFrame::from_unused_spec(paddr, metadata, pre).1.inv(),
    { }

    pub open spec fn meta_spec(&self, pre: UniqueFrameModel) -> PPtr<M>
        recommends
            pre.inv(),
    {
        M::cast_to_spec(&pre.slot.storage.value())
    }

    pub open spec fn replace_spec(&self, metadata: M, pre: UniqueFrameModel)
        -> UniqueFrameModel
        recommends
            pre.inv(),
    {
        let storage = MemContents::Init(metadata.write_as_spec());
        UniqueFrameModel {
            slot: MetaSlotModel {
                storage,
                ..pre.slot
            }
        }
    }
}

impl UniqueFrameModel {
    pub open spec fn from_raw_spec(region: MetaRegionModel, paddr: Paddr) -> Self {
        Self {
            slot: region.slots[frame_to_index(paddr)],
        }
    }
}

impl<M: AnyFrameMeta> UniqueFrameOwner<M> {
    pub closed spec fn from_raw_owner(region: MetaRegionOwners, paddr: Paddr) -> Self;

//    pub open spec fn from_raw_spec(region: MetaRegionOwners, paddr: Paddr) -> Self {
//        Self {
//            slot: Tracked(region.slot_owners[frame_to_index(paddr)]),
//        }
//    }
}

impl<M: AnyFrameMeta> AnyFrameMeta for Link<M>
{
    fn on_drop(&mut self) { }

    fn is_untyped(&self) -> bool { false }

    spec fn vtable_ptr(&self) -> usize;

    spec fn cast_to_spec(x: &MetaSlotStorage) -> PPtr<Self>;

    #[verifier::external_body]
    fn cast_to(x: &MetaSlotStorage) -> PPtr<Self> {
        unimplemented!()
    }

    spec fn write_as_spec(&self) -> MetaSlotStorage;

    #[verifier::external_body]
    fn write_as(&self) -> MetaSlotStorage {
        unimplemented!()
    }
}

}