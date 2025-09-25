use vstd::prelude::*;
use vstd::simple_pptr::{self, *};
use vstd::cell;
use vstd::atomic::*;

use vstd_extra::ownership::*;
use vstd_extra::cast_ptr::*;

use crate::prelude::*;

use std::marker::PhantomData;

verus! {

/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta: Repr<MetaSlotStorage> {
    exec fn on_drop(&mut self) {}

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;
}

#[rustc_has_incoherent_inherent_impls]
pub struct UniqueFrame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta> {
    pub slot: Tracked<MetaSlotOwner>,
    pub data: M,
}

pub ghost struct UniqueFrameModel {
    pub slot: MetaSlotModel,
//    pub data: M,
}

impl<M: AnyFrameMeta> Inv for UniqueFrameOwner<M> {
    open spec fn inv(&self) -> bool {
    &&& self.slot@.inv()
    &&& self.slot@.ref_count@.value() == REF_COUNT_UNIQUE
    &&& self.slot@.vtable_ptr@.is_init()
    &&& self.slot@.storage@.is_init()
    &&& self.slot@.storage@.value() == self.data.to_repr()
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

    pub open spec fn replace_spec(&self, metadata: M, pre: UniqueFrameModel)
        -> UniqueFrameModel
        recommends
            pre.inv(),
    {
        let storage = MemContents::Init(metadata.to_repr());
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

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> UniqueFrameOwner<M> {
    pub closed spec fn from_raw_owner(region: MetaRegionOwners, paddr: Paddr) -> Self;
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Link<M> {
    pub open spec fn into_spec(self) -> StoredLink {
        let next = match self.next {
            Some(link) => Some(link.addr),
            None => None
        };
        let prev = match self.prev {
            Some(link) => Some(link.addr),
            None => None
        };
        StoredLink {
            next: next,
            prev: prev,
            slot: self.meta.to_repr(),
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> (res: StoredLink)
        ensures res == self.into_spec()
    {
        let next = match self.next {
            Some(link) => Some(link.addr),
            None => None
        };
        let prev = match self.prev {
            Some(link) => Some(link.addr),
            None => None
        };
        StoredLink {
            next: next,
            prev: prev,
            slot: self.meta.to_repr(),
        }
    }
}

impl StoredLink {
    pub open spec fn into_spec<M: AnyFrameMeta + Repr<MetaSlotInner>>(self) -> Link<M> {
        let next = match self.next {
            Some(addr) => Some(ReprPtr {
                addr: addr,
                ptr: PPtr::<MetaSlotStorage>(addr, PhantomData),
                _T: PhantomData}),
            None => None
        };
        let prev = match self.prev {
            Some(addr) => Some(ReprPtr {
                addr: addr,
                ptr: PPtr::<MetaSlotStorage>(addr, PhantomData),
                _T: PhantomData}),
            None => None
        };
        Link::<M> {
            next: next,
            prev: prev,
            meta: M::from_repr(self.slot)
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<M: AnyFrameMeta + Repr<MetaSlotInner>>(self) -> (res: Link<M>)
        requires M::wf(self.slot)
        ensures res == self.into::<M>()
    {
        let next = match self.next {
            Some(addr) => Some(ReprPtr {
                addr: addr,
                ptr: PPtr::<MetaSlotStorage>::from_addr(addr),
                _T: PhantomData}),
            None => None
        };
        let prev = match self.prev {
            Some(addr) => Some(ReprPtr {
                addr: addr,
                ptr: PPtr::<MetaSlotStorage>::from_addr(addr),
                _T: PhantomData}),
            None => None
        };
        Link::<M> {
            next: next,
            prev: prev,
            meta: M::from_repr(self.slot)
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Repr<MetaSlotStorage> for Link<M> {

    open spec fn wf(r: MetaSlotStorage) -> bool {
        match r {
            MetaSlotStorage::FrameLink(link) => M::wf(link.slot),
            _ => false,
        }
    }

    open spec fn to_repr_spec(self) -> MetaSlotStorage {
        MetaSlotStorage::FrameLink(self.into())
    }

    fn to_repr(self) -> MetaSlotStorage {
        MetaSlotStorage::FrameLink(self.into())
    }

    open spec fn from_repr_spec(r: MetaSlotStorage) -> Self {
        r.get_link().unwrap().into()
    }

    fn from_repr(r: MetaSlotStorage) -> Self
    {
        r.get_link().unwrap().into()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
        unimplemented!()
//        &r.get_link().unwrap().into()
    }

    proof fn from_to_repr(self)
    {
        <M as Repr<MetaSlotInner>>::from_to_repr(self.meta);
        admit()
    }

    proof fn to_from_repr(r: MetaSlotStorage)
    {
        M::to_from_repr(r.get_link().unwrap().slot)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> AnyFrameMeta for Link<M>
{
    fn on_drop(&mut self) { }

    fn is_untyped(&self) -> bool { false }

    spec fn vtable_ptr(&self) -> usize;
}

}