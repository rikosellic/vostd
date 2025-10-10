use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, *};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::prelude::*;

use std::marker::PhantomData;

verus! {

/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta: Repr<MetaSlotStorage> {
    exec fn on_drop(&mut self) {
    }

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

impl StoredLink {
    pub open spec fn into_spec<M: AnyFrameMeta + Repr<MetaSlotInner>>(self) -> Link<M> {
        let next = match self.next {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>(addr, PhantomData),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        let prev = match self.prev {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>(addr, PhantomData),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        Link::<M> { next: next, prev: prev, meta: M::from_repr(self.slot) }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<M: AnyFrameMeta + Repr<MetaSlotInner>>(self) -> (res: Link<M>)
        requires
            M::wf(self.slot),
        ensures
            res == self.into::<M>(),
    {
        let next = match self.next {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>::from_addr(addr),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        let prev = match self.prev {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>::from_addr(addr),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        Link::<M> { next: next, prev: prev, meta: M::from_repr(self.slot) }
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

    fn from_repr(r: MetaSlotStorage) -> Self {
        r.get_link().unwrap().into()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
        unimplemented!()
        //        &r.get_link().unwrap().into()

    }

    proof fn from_to_repr(self) {
        <M as Repr<MetaSlotInner>>::from_to_repr(self.meta);
        admit()
    }

    proof fn to_from_repr(r: MetaSlotStorage) {
        M::to_from_repr(r.get_link().unwrap().slot)
    }

    proof fn to_repr_wf(self) {
        <M as Repr<MetaSlotInner>>::to_repr_wf(self.meta)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> AnyFrameMeta for Link<M> {
    fn on_drop(&mut self) {
    }

    fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;
}

} // verus!
