use vstd::prelude::*;
use vstd::cell::{PCell};
use vstd::simple_pptr::{PPtr};
use vstd::atomic_ghost::*;
use vstd::atomic::PAtomicU64;

use super::*;

use core::mem::ManuallyDrop;
use core::ops::Deref;

#[allow(unused_imports)]
use vstd_extra::manually_drop::*;

verus! {

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    FrameLink(Link),
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
