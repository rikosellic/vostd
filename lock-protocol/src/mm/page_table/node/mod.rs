pub mod child;
pub mod entry;

use std::cell::Cell;
use std::cell::SyncUnsafeCell;
use std::marker::PhantomData;
use std::ops::Range;

use entry::Entry;
use vstd::cell::PCell;
use vstd::prelude::*;

#[allow(unused_imports)]
use child::*;
use crate::mm::meta::AnyFrameMeta;
use crate::mm::nr_subpage_per_huge;
use crate::mm::untyped::UFrame;
use crate::mm::Paddr;
use crate::mm::PageTableEntryTrait;
use crate::mm::PagingConstsTrait;
use crate::mm::PagingConsts;

use crate::mm::frame::Frame;
use crate::mm::PagingLevel;

use crate::sync::spin;
// TODO: Use a generic style?
use crate::x86_64::paddr_to_vaddr;

verus! {

// #[derive(Debug)] // TODO: Debug for PageTableNode
pub(super) type PageTableNode<
    // E: PageTableEntryTrait = PageTableEntry,
    // C: PagingConstsTrait = PagingConsts,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
    // T: AnyFrameMeta
> = Frame<PageTablePageMeta<E, C>>;

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
// #[derive(Debug)] // TODO: Debug for PageTablePageMeta
impl<E: PageTableEntryTrait, C: PagingConstsTrait> PageTableNode<E, C>
{
    /// The level of the page table node.
    #[verifier::external_body] // TODO
    pub(super) fn level(&self) -> (res: PagingLevel)
    ensures
        0 <= res <= C::NR_LEVELS_SPEC(),
    {
        self.meta().level
    }

    /// Gets to an accessible guard by pertaining the lock.
    ///
    /// This should be an unsafe function that requires the caller to ensure
    /// that preemption is disabled while the lock is held, or if the page is
    /// not shared with other CPUs.
    pub(super) fn lock(self) -> PageTableLock<E, C> {
        unsafe { self.meta().lock.lock() }
        PageTableLock::<E, C> { frame: Some(self) }
    }

    /// Activates the page table assuming it is a root page table.
    ///
    /// Here we ensure not dropping an active page table by making a
    /// processor a page table owner. When activating a page table, the
    /// reference count of the last activated page table is decremented.
    /// And that of the current page table is incremented.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the page table to be activated has
    /// proper mappings for the kernel and has the correct const parameters
    /// matching the current CPU.
    ///
    /// # Panics
    ///
    /// Only top-level page tables can be activated using this function.
    pub(crate) unsafe fn activate(&self) {
        // TODO: Implement activate for PageTableNode
        // use crate::{
        //     arch::mm::{activate_page_table, current_page_table_paddr},
        //     mm::CachePolicy,
        // };

        // assert_eq!(self.level(), C::NR_LEVELS);

        // let last_activated_paddr = current_page_table_paddr();
        // if last_activated_paddr == self.start_paddr() {
        //     return;
        // }

        // activate_page_table(self.clone().into_raw(), CachePolicy::Writeback);

        // // Restore and drop the last activated page table.
        // // SAFETY: The physical address is valid and points to a forgotten page table node.
        // drop(unsafe { Self::from_raw(last_activated_paddr) });
    }

    /// Activates the (root) page table assuming it is the first activation.
    ///
    /// It will not try dropping the last activate page table. It is the same
    /// with [`Self::activate()`] in other senses.
    pub(super) unsafe fn first_activate(&self) {
        // TODO: Implement first_activate for PageTableNode
        // use crate::{arch::mm::activate_page_table, mm::CachePolicy};

        // activate_page_table(self.clone().into_raw(), CachePolicy::Writeback);
    }
}

/// A owned mutable guard that holds the lock of a page table node.
///
/// This should be used as a linear type, i.e, it shouldn't be dropped. The
/// only way to destruct the type must be [`PageTableLock::unlock`].
// #[derive(Debug)] // TODO: Debug for PageTableLock
pub struct PageTableLock<
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
> {
    // We need to wrap it in `Option` to perform the linear type check.
    pub frame: Option<Frame<PageTablePageMeta<E, C>>>,
}

impl<E: PageTableEntryTrait, C: PagingConstsTrait> PageTableLock<E, C> {
    /// Borrows an entry in the node at a given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is not within the bound of
    /// [`nr_subpage_per_huge<C>`].
    // pub(super) fn entry(&mut self, idx: usize) -> Entry<'_, E, C> { // TODO: mut?
    pub(super) fn entry(&self, idx: usize) -> Entry<'_, E, C>
    requires
        idx < nr_subpage_per_huge(),
    {
        // assert!(idx < nr_subpage_per_huge::<C>());
        assert(idx < nr_subpage_per_huge());
        // SAFETY: The index is within the bound.
        unsafe { Entry::new_at(self, idx) }
    }

    /// Gets the physical address of the page table node.
    pub(super) fn paddr(&self) -> Paddr
    requires
        self.frame.is_some(),
    {
        self.frame.as_ref().unwrap().start_paddr()
    }

    /// Gets the level of the page table node.
    pub(super) fn level(&self) -> PagingLevel {
        self.meta().level
    }

    /// Gets the tracking status of the page table node.
    pub(super) fn is_tracked(&self) -> MapTrackingStatus {
        self.meta().is_tracked
    }

    /// Allocates a new empty page table node.
    ///
    /// This function returns a locked owning guard.
    // TODO: Implement alloc for PageTableLock
    #[verifier::external_body]
    pub(super) fn alloc(level: PagingLevel, is_tracked: MapTrackingStatus) -> Self {
        // let meta = PageTablePageMeta::new_locked(level, is_tracked);
        // let frame = FrameAllocOptions::new()
        //     .zeroed(true)
        //     .alloc_frame_with(meta)
        //     .expect("Failed to allocate a page table node");
        // // The allocated frame is zeroed. Make sure zero is absent PTE.
        // debug_assert!(E::new_absent().as_bytes().iter().all(|&b| b == 0));

        // Self { frame: Some(frame) }
        unimplemented!()
    }

    /// Unlocks the page table node.
    // TODO: Implement unlock for PageTableLock
    #[verifier::external_body]
    pub(super) fn unlock(&mut self) -> PageTableNode<E, C> {
        // // Release the lock.
        // // SAFETY:
        // //  - The lock stays at the metadata slot so it's pinned.
        // //  - The constructor of the node guard ensures that the lock is held,
        // //    and no preemption is allowed.
        // unsafe { self.meta().lock.unlock() };

        // self.frame.take().unwrap()
        unimplemented!()
    }

    /// Converts the guard into a raw physical address.
    ///
    /// It will not release the lock. It may be paired with [`Self::from_raw_paddr`]
    /// to manually manage pointers.
    // TODO: Implement into_raw_paddr for PageTableLock
    #[verifier::external_body]
    pub(super) fn into_raw_paddr(self) -> Paddr {
        // let this = ManuallyDrop::new(self);
        // this.paddr()
        unimplemented!()
    }

    /// Converts a raw physical address to a guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the physical address is valid and points to
    /// a forgotten page table node (see [`Self::into_raw_paddr`]) that is not
    /// yet restored.
    pub(super) unsafe fn from_raw_paddr(paddr: Paddr) -> Self {
        let frame = PageTableNode::from_raw(paddr);
        Self { frame: Some(frame) }
    }

    /// Gets the number of valid PTEs in the node.
    // TODO: Implement nr_children for PageTableLock
    #[verifier::external_body]
    pub(super) fn nr_children(&self) -> u16 {
        // SAFETY: The lock is held so we have an exclusive access.
        // unsafe { *self.meta().nr_children.get() }
        // self.meta().nr_children.into()
        unimplemented!()
    }

    /// If the page table node is detached from its parent.
    // TODO: Implement astray for PageTableLock
    // #[verifier::external_body]
    // // pub(super) fn astray_mut(&mut self) -> &mut bool {
    // pub(super) fn astray_mut(&mut self) -> &mut bool {
    //     // SAFETY: The lock is held so we have an exclusive access.
    //     unsafe { &mut *self.meta().astray.get() }
    // }

    /// Reads a non-owning PTE at the given index.
    ///
    /// A non-owning PTE means that it does not account for a reference count
    /// of the a page if the PTE points to a page. The original PTE still owns
    /// the child page.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    // TODO: Implement read_pte for PageTableLock
    #[verifier::external_body]
    unsafe fn read_pte(&self, idx: usize) -> E {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        // let ptr = paddr_to_vaddr(self.paddr()) as *mut E;
        // // SAFETY:
        // // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // // - All page table entries are aligned and accessed with atomic operations only.
        // unsafe { load_pte(ptr.add(idx), Ordering::Relaxed) }

        unimplemented!()
    }

    /// Writes a page table entry at a given index.
    ///
    /// This operation will leak the old child if the old PTE is present.
    ///
    /// The child represented by the given PTE will handover the ownership to
    /// the node. The PTE will be rendered invalid after this operation.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  1. The index must be within the bound;
    ///  2. The PTE must represent a child compatible with this page table node
    ///     (see [`Child::is_compatible`]).
    // TODO: Implement write_pte for PageTableLock
    #[verifier::external_body]
    unsafe fn write_pte(&mut self, idx: usize, pte: E) {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        // let ptr = paddr_to_vaddr(self.paddr()) as *mut E;
        // // SAFETY:
        // // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // // - All page table entries are aligned and accessed with atomic operations only.
        // unsafe { store_pte(ptr.add(idx), pte, Ordering::Release) }

        unimplemented!()
    }

    /// Gets the mutable reference to the number of valid PTEs in the node.
    // #[verifier::external_body]
    // fn nr_children_mut(&mut self) -> &mut u16 {
    //     // SAFETY: The lock is held so we have an exclusive access.
    //     unsafe { &mut *self.meta().nr_children.get() }
    // }

    // TODO: Implement
    #[verifier::external_body]
    fn meta(&self) -> &PageTablePageMeta<E, C> {
        // self.frame.as_ref().unwrap().meta()
        unimplemented!()
    }
}

// TODO: Implement Drop for PageTableLock
// impl<E: PageTableEntryTrait, C: PagingConstsTrait> Drop for PageTableLock<E, C> {
//     fn drop(&mut self) {
//         if self.frame.is_some() {
//             panic!("Dropping `PageTableLock` instead of `unlock` it")
//         }
//     }
// }

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
// #[derive(Debug)] // TODO: Debug for PageTablePageMeta
pub struct PageTablePageMeta<
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
> {
    /// The lock for the page table page.
    pub lock: spin::queued::LockBody,

    /// The number of valid PTEs. It is mutable if the lock is held.
    // TODO: PCell or Cell?
    // pub nr_children: SyncUnsafeCell<u16>,
    pub nr_children: PCell<u16>,

    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub astray: PCell<bool>,

    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// Whether the pages mapped by the node is tracked.
    pub is_tracked: MapTrackingStatus,
    pub _phantom: core::marker::PhantomData<(E, C)>,
}

/// Describe if the physical address recorded in this page table refers to a
/// page tracked by metadata.
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

impl<E: PageTableEntryTrait, C: PagingConstsTrait> PageTablePageMeta<E, C>
where
    // [(); C::NR_LEVELS as usize]:,
{
    
    // TODO: Implement
    #[verifier::external_body]
    pub fn new_locked(level: PagingLevel, is_tracked: MapTrackingStatus) -> Self {
        Self {
            // nr_children: SyncUnsafeCell::new(0),
            // astray: SyncUnsafeCell::new(false),
            nr_children: PCell::new(0u16).0,
            astray: PCell::new(false).0,
            level,
            lock: spin::queued::LockBody::new_locked(),
            is_tracked,
            _phantom: PhantomData,
        }
    }
}

// SAFETY: The layout of the `PageTablePageMeta` is ensured to be the same for
// all possible generic parameters. And the layout fits the requirements.
// unsafe
impl<E: PageTableEntryTrait, C: PagingConstsTrait> AnyFrameMeta for PageTablePageMeta<E, C>
where
    // [(); C::NR_LEVELS as usize]:,
{
    // TODO: Implement AnyFrameMeta for PageTablePageMeta
}

}
