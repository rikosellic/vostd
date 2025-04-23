pub mod impls;
pub mod model;
pub mod specs;

use core::{mem::ManuallyDrop, mem::size_of, cell::UnsafeCell};
use model::MetaSlotModel;
use vstd::{prelude::*, cell::*, atomic::*, atomic_ghost::*};
use crate::page::Page;

verus! {

/// Represents the usage of a page.
#[repr(u8)]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum PageUsage {
    // The zero variant is reserved for the unused type. Only an unused page
    // can be designated for one of the other purposes.
    #[allow(dead_code)]
    Unused = 0,
    /// The page is reserved or unusable. The kernel should not touch it.
    #[allow(dead_code)]
    Reserved = 1,

    /// The page is used as a frame, i.e., a page of untyped memory.
    Frame = 32,

    /// The page is used by a page table.
    PageTable = 64,
    /// The page stores metadata of other pages.
    Meta = 65,
    /// The page stores the kernel such as kernel code, data, etc.
    Kernel = 66,
}

} // verus!

verus! {

use model::{ActualUsage, MetaSlotState};

#[allow(non_camel_case_types)]
struct_with_invariants! {

#[repr(C, align(16))]
pub struct MetaSlot {
    /// The metadata of the page.
    ///
    /// It is placed at the beginning of a slot because:
    ///  - the implementation can simply cast a `*const MetaSlot`
    ///    to a `*const PageMeta` for manipulation;
    ///  - the subsequent fields can utilize the end padding of the
    ///    the inner union to save space.
    pub _inner: PCell<MetaSlotInner>,
    /// To store [`PageUsage`].
    pub usage: AtomicU8<_, ActualUsage, _>,
    pub ref_count: PAtomicU32,
}

pub open spec fn wf(&self) -> bool {
    invariant on usage with (_inner) is (v: u8, g: ActualUsage) {
        match g {
            ActualUsage::Unused(perm) => {
            &&& v == 0
            &&& perm.id() == _inner.id()
            &&& perm.is_uninit()
            },
            ActualUsage::Used(usage) => {
            &&& v == usage.as_u8()
            &&& v != 0
            },
        }
    }
}
}
} // verus!

verus! {

pub union MetaSlotInner {
    _frame: ManuallyDrop<FrameMeta>,
    _pt: ManuallyDrop<PageTablePageMeta>,
    _others: [u8; 0],
}

}

verus! {
/// All page metadata types must implemented this sealed trait,
/// which ensures that each fields of `PageUsage` has one and only
/// one metadata type corresponding to the usage purpose. Any user
/// outside this module won't be able to add more metadata types
/// and break assumptions made by this module.
///
/// If a page type needs specific drop behavior, it should specify
/// when implementing this trait. When we drop the last handle to
/// this page, the `on_drop` method will be called.
pub trait PageMeta: Sync + Sized {
    spec fn on_drop_spec(page: &Page<Self>) -> (res: Page<Self>);
    spec fn get_usage_spec() -> PageUsage;
    spec fn default_spec() -> Self;

    fn on_drop(page: &mut Page<Self>)
        ensures
            page == Self::on_drop_spec(page)
    ;

    #[verifier::when_used_as_spec(get_usage_spec)]
    fn get_usage() -> (res: PageUsage)
        ensures
            res == Self::get_usage_spec(),
            res != PageUsage::Unused,
    ;

    #[verifier::when_used_as_spec(default_spec)]
    fn default() -> (res: Self)
        ensures
            res == Self::default_spec()
    ;
}

}

verus! {

#[repr(C)]
#[derive(Debug)]
pub struct FrameMeta {
    // If not doing so, the page table metadata would fit
    // in the front padding of meta slot and make it 12 bytes.
    // We make it 16 bytes. Further usage of frame metadata
    // is welcome to exploit this space.
    _unused_for_layout_padding: [u8; 8],
}

pub type PagingLevel = u8;

#[repr(C)]
pub struct PageTablePageMetaInner {
    pub level: PagingLevel,
    pub nr_children: u16,
}

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
#[repr(C)]
pub struct PageTablePageMeta
{
    pub lock: PAtomicU8,
    pub inner: PCell<PageTablePageMetaInner>,
}

} // verus!

verus! {

impl Default for FrameMeta {
    fn default() -> Self {
        Self {
            _unused_for_layout_padding: [0; 8],
        }
    }
}
} // verus!

verus! {
impl Default for PageTablePageMetaInner {
    fn default() -> Self {
        Self {
            level: 0,
            nr_children: 0,
        }
    }
}
} // verus!

verus! {

impl Default for PageTablePageMeta {
    fn default() -> Self {
        let (lock, Tracked(lock_perm)) = PAtomicU8::new(0);
        let (inner, Tracked(inner_perm)) = PCell::new(PageTablePageMetaInner::default());

        Self {
            lock,
            inner,
        }
    }
}

} // verus!
