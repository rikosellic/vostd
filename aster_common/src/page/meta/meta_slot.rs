use vstd::atomic::PAtomicU64;
use vstd::atomic::PAtomicU8;
use vstd::cell::{self, PCell};
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::*;

use core::mem::ManuallyDrop;
use core::ops::Deref;

use std::marker::PhantomData;

use crate::prelude::*;

#[allow(unused_imports)]
use vstd_extra::manually_drop::*;

verus! {

pub open spec fn get_slot_spec(paddr: Paddr) -> (res: PPtr<MetaSlot>)
    recommends
        paddr % 4096 == 0,
        paddr < MAX_PADDR(),
{
    let slot = frame_to_meta(paddr);
    PPtr(slot, PhantomData::<MetaSlot>)
}

pub struct MetaSlotInner {}

pub struct StoredLink {
    pub next: Option<Paddr>,
    pub prev: Option<Paddr>,
    pub slot: MetaSlotInner,
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
            _ => None,
        }
    }

    #[verifier::when_used_as_spec(get_link_spec)]
    pub fn get_link(self) -> (res: Option<StoredLink>)
        ensures
            res == self.get_link_spec(),
    {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None,
        }
    }

    pub open spec fn get_node_spec(self) -> Option<StoredPageTablePageMeta> {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None,
        }
    }

    #[verifier::when_used_as_spec(get_node_spec)]
    pub fn get_node(self) -> (res: Option<StoredPageTablePageMeta>)
        ensures
            res == self.get_node_spec(),
    {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None,
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
{
    admit()
}

pub proof fn size_of_meta_slot()
    ensures
        size_of::<MetaSlot>() == 64,
        align_of::<MetaSlot>() == 8,
{
    admit()
}

#[inline(always)]
#[verifier::allow_in_spec]
pub const fn meta_slot_size() -> (res: usize)
    returns
        64usize,
{
    proof {
        size_of_meta_slot();
    }
    size_of::<MetaSlot>()
}

impl MetaSlot {
    pub fn cast_storage<T: Repr<MetaSlotStorage>>(
        &self,
        addr: usize,
        Tracked(owner): Tracked<&MetaSlotOwner>,
    ) -> (res: ReprPtr<MetaSlotStorage, T>)
        requires
            self.wf(owner),
            owner.inv(),
            addr == owner.storage@.addr(),
        ensures
            res.ptr == owner.storage@.pptr(),
            res.addr == addr,
    {
        ReprPtr::<MetaSlotStorage, T> { addr: addr, ptr: self.storage, _T: PhantomData }
    }
}

} // verus!
