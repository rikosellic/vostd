use vstd::prelude::*;
use vstd::cell::{self, PCell};
use vstd::simple_pptr::{self, PPtr};
use vstd::atomic_ghost::*;
use vstd::atomic::PAtomicU64;

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

pub struct LinkOuter {
    pub next: Option<PPtr<LinkOuter>>,
    pub prev: Option<PPtr<LinkOuter>>,
}

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    FrameLink(LinkOuter),
    PTNode(PageTablePageMetaInner),
}

#[rustc_has_incoherent_inherent_impls]
pub struct MetaSlot {
    pub storage: PCell<MetaSlotStorage>,
    pub ref_count: PAtomicU64,
    pub vtable_ptr: PPtr<usize>,
    pub in_list: PAtomicU64,
}


global layout MetaSlot is size == 64, align == 8;


pub broadcast proof fn lemma_meta_slot_size()
    ensures
        #[trigger] size_of::<MetaSlot>() == META_SLOT_SIZE(),
{ }

pub proof fn size_of_meta_slot()
    ensures
        size_of::<MetaSlot>() == 64,
        align_of::<MetaSlot>() == 8,
{ }

#[inline(always)]
#[verifier::allow_in_spec]
pub const fn meta_slot_size() -> (res: usize)
    returns 64usize
{
    size_of::<MetaSlot>()
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
            paddr < MAX_PADDR(),
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
                    storage: cell::MemContents::Init(metadata.write_as()),
                    ref_count: rc,
                    vtable_ptr: simple_pptr::MemContents::Init(metadata.vtable_ptr()),
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
            paddr < MAX_PADDR(),
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
            paddr < MAX_PADDR(),
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

/*impl MetaSlotInner {

    pub open spec fn borrow_pt_spec(& self) -> & PageTablePageMeta
    {
        ex_manually_drop_deref_spec(&get_union_field::<MetaSlotInner, ManuallyDrop<PageTablePageMeta>>(*self, "_pt"))
    }

    #[verifier::external_body]
    pub fn borrow_pt(&self)
        -> (res: &PageTablePageMeta)
        ensures
            res == self.borrow_pt_spec(),
    {
        unsafe {
            self._pt.deref()
        }
    }

    pub open spec fn borrow_frame_spec(&self) -> & FrameMeta
    {
        ex_manually_drop_deref_spec(&get_union_field::<MetaSlotInner, ManuallyDrop<FrameMeta>>(*self, "_frame"))
    }

    #[verifier::external_body]
    pub fn borrow_frame(&self)
        -> (res: &FrameMeta)
        ensures
            res == self.borrow_frame_spec(),
    {
        unsafe {
            self._frame.deref()
        }
    }
}

impl MetaSlot {

    pub open spec fn borrow_pt_spec<'a>(&'a self, inner_perm: &'a PointsTo<MetaSlotInner>) -> &'a PageTablePageMeta
        recommends
            inner_perm.is_init(),
            is_variant(inner_perm.value(), "_pt"),
    {
        ex_manually_drop_deref_spec(&get_union_field::<MetaSlotInner, ManuallyDrop<PageTablePageMeta>>(inner_perm.value(), "_pt"))
    }

    pub fn borrow_pt<'a>(&'a self,
        inner_perm: Tracked<&'a PointsTo<MetaSlotInner>>)
        -> (res: &'a PageTablePageMeta)
        requires
            //self.wf(),
            self._inner.id() == inner_perm@.id(),
            inner_perm@.is_init(),
            is_variant(inner_perm@.value(), "_pt"),
        ensures
            res == self.borrow_pt_spec(inner_perm@),
    {
        let inner: &MetaSlotInner = self._inner.borrow(inner_perm);
        assert(is_variant(inner, "_pt"));
        inner.borrow_pt()
    }

    pub open spec fn borrow_frame_spec<'a>(&'a self, inner_perm: &'a PointsTo<MetaSlotInner>) -> &'a FrameMeta
        recommends
            inner_perm.is_init(),
            is_variant(inner_perm.value(), "_frame"),
    {
        ex_manually_drop_deref_spec(&get_union_field::<MetaSlotInner, ManuallyDrop<FrameMeta>>(inner_perm.value(), "_frame"))
    }

    pub fn borrow_frame<'a>(&'a self,
        Tracked(inner_perm): Tracked<&'a PointsTo<MetaSlotInner>>)
        -> (res: &'a FrameMeta)
        requires
            //self.wf(),
            self._inner.id() == inner_perm.id(),
            inner_perm.is_init(),
            is_variant(inner_perm.value(), "_frame"),
        ensures
            res == self.borrow_frame_spec(inner_perm),
    {
        let inner: &MetaSlotInner = self._inner.borrow(Tracked(inner_perm));
        assert(is_variant(inner, "_frame"));
        inner.borrow_frame()
    }

}

} // verus!

verus! {
impl Default for MetaSlotInner {
    #[verifier::external_body]
    fn default() -> Self {
        Self {
            _frame: ManuallyDrop::new(FrameMeta::default()),
        }
    }
}*/
}
