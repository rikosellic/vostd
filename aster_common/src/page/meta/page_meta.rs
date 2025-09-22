use vstd::prelude::*;
use vstd::simple_pptr::*;

use super::super::Frame;
use super::frame_to_meta;
use super::PageUsage;

use crate::prelude::*;

use vstd::cell::{PCell, PointsTo};
use vstd::atomic::{PAtomicU8, PermissionU8};
use vstd_extra::cast_ptr::*;
use crate::mm::*;
use crate::x86_64::page_table_entry::PageTableEntry;
use crate::x86_64::paging_consts::PagingConsts;
use core::marker::PhantomData;

verus! {

/*#[allow(non_snake_case)]
pub trait PageMeta: Sync + Sized {
    spec fn USAGE_spec() -> PageUsage;

    proof fn used()
        ensures
            Self::USAGE_spec() != PageUsage::Unused,
    ;

    #[verifier::when_used_as_spec(USAGE_spec)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    ;

    spec fn on_drop_spec(page: Page<Self>) -> (res: Page<Self>);

    fn on_drop(page: &mut Page<Self>)
        ensures
            page == Self::on_drop_spec(*old(page)),
    ;
}*/

#[rustc_has_incoherent_inherent_impls]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum MapTrackingStatus {
    /// The page table node cannot contain references to any pages. It can only
    /// contain references to child page table nodes.
    NotApplicable,
    /// The mapped pages are not tracked by metadata. If any child page table
    /// nodes exist, they should also be tracked.
    Untracked,
    /// The mapped pages are tracked by metadata. If any child page table nodes
    /// exist, they should also be tracked.
    Tracked,
}

impl Default for MapTrackingStatus {
    fn default() -> Self {
        MapTrackingStatus::NotApplicable
    }
}

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
#[rustc_has_incoherent_inherent_impls]
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The number of valid PTEs. It is mutable if the lock is held.
    pub nr_children: /*SyncUnsafeCell<*/u16/*>*/,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub stray: /*SyncUnsafeCell<*/bool/*>*/,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// The lock for the page table page.
    pub lock: PAtomicU8,
    pub _phantom: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub open spec fn into_spec(self) -> PageTablePageMetaOuter {
        PageTablePageMetaOuter {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> (res: PageTablePageMetaOuter)
        ensures res == self.into_spec()
    {
        PageTablePageMetaOuter {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }
}

impl PageTablePageMetaOuter {
    pub open spec fn into_spec<C: PageTableConfig>(self) -> PageTablePageMeta<C> {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<C: PageTableConfig>(self) -> (res: PageTablePageMeta<C>)
        ensures res == self.into_spec::<C>()
    {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }
}

spec fn drop_tree_spec<C: PageTableConfig>(_page: Frame<PageTablePageMeta<C>>) -> Frame<PageTablePageMeta<C>>;

#[verifier::external_body]
extern  fn drop_tree<C: PageTableConfig>(_page: &mut Frame<PageTablePageMeta<C>>)
    ensures
        _page == drop_tree_spec::<C>(*old(_page)),
;

impl<C: PageTableConfig> Repr<MetaSlotStorage> for PageTablePageMeta<C> {

    open spec fn wf(r: MetaSlotStorage) -> bool {
        match r {
            MetaSlotStorage::PTNode(_) => true,
            _ => false,
        }
    }

    open spec fn to_repr_spec(self) -> MetaSlotStorage {
        MetaSlotStorage::PTNode(self.into())
    }

    fn to_repr(self) -> MetaSlotStorage {
        MetaSlotStorage::PTNode(self.into())
    }

    open spec fn from_repr_spec(r: MetaSlotStorage) -> Self {
        r.get_node().unwrap().into()
    }

    fn from_repr(r: MetaSlotStorage) -> Self {
        r.get_node().unwrap().into()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
        unimplemented!()
//        &r.get_node().unwrap().into()
    }

    proof fn from_to_repr(self)
        ensures Self::from_repr(self.to_repr()) == self
    { }

    proof fn to_from_repr(r: MetaSlotStorage)
        ensures Self::from_repr(r).to_repr() == r
    { }
}

impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    fn on_drop(&mut self) { }

    fn is_untyped(&self) -> bool { false }

    spec fn vtable_ptr(&self) -> usize;
}

/*impl PageMeta for PageTablePageMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::PageTable
    }

    proof fn used() {
        assert(PageUsage::PageTable != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::PageTable
    }

    closed spec fn on_drop_spec(_page: Page<Self>) -> (res: Page<Self>) {
        drop_tree_spec(_page)
    }

    fn on_drop(_page: &mut Page<Self>)
        ensures
            _page == Self::on_drop_spec(*old(_page)),
    {
        drop_tree(_page)
    }
}*/

/*impl PageTablePageMeta {
    pub open spec fn new_locked_spec(
        level: PagingLevel,
        is_tracked: MapTrackingStatus,
        res: PageTablePageMetaModel,
    ) -> bool {
        &&& res.lock@.value == 1
        &&& res.inner.opt_value() == Some(
            { PageTablePageMetaInner { level, nr_children: 0, is_tracked } },
        )
    }

    pub fn new_locked(level: PagingLevel, is_tracked: MapTrackingStatus) -> (res: (
        Self,
        Tracked<PageTablePageMetaModel>,
    ))
        ensures
            res.1@.relate(&res.0),
            res.1@.inner.is_init(),
            Self::new_locked_spec(level, is_tracked, res.1@),
    {
        let (inner, Tracked(perm)) = PCell::new(
            PageTablePageMetaInner { level, nr_children: 0, is_tracked },
        );
        let (lock, Tracked(lk_perm)) = PAtomicU8::new(1);
        let tracked model = PageTablePageMetaModel { lock: lk_perm, inner: perm };
        let meta = Self { lock, inner, _phantom: PhantomData };
        (meta, Tracked(model))
    }
}*/

} // verus!
verus! {

#[derive(Debug, Default)]
#[repr(C)]
pub struct MetaPageMeta {}

/*impl PageMeta for MetaPageMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::Meta
    }

    proof fn used() {
        assert(PageUsage::Meta != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::Meta
    }

    #[verifier::inline]
    open spec fn on_drop_spec(_page: Page<Self>) -> (res: Page<Self>) {
        _page
    }

    fn on_drop(_page: &mut Page<Self>)
        ensures
            _page == Self::on_drop_spec(*old(_page)),
    {
    }
}*/

} // verus!
verus! {

#[derive(Debug, Default)]
#[repr(C)]
pub struct KernelMeta {}

/*impl PageMeta for KernelMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::Kernel
    }

    proof fn used() {
        assert(PageUsage::Kernel != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::Kernel
    }

    #[verifier::inline]
    open spec fn on_drop_spec(_page: Page<Self>) -> (res: Page<Self>) {
        _page
    }

    fn on_drop(_page: &mut Page<Self>)
        ensures
            _page == Self::on_drop_spec(*old(_page)),
    {
    }
}*/

} // verus!
