mod child;

use std::marker::PhantomData;
use std::ops::Range;

use vstd::prelude::*;

#[allow(unused_imports)]
use child::*;
use crate::meta::AnyFrameMeta;
use crate::untyped::UFrame;
use crate::PageTableEntryTrait;
use crate::PageTableEntry;
use crate::PagingConstsTrait;
use crate::PagingConsts;

use crate::mm::frame::Frame;
use crate::PagingLevel;

verus! {

// #[derive(Debug)] // TODO: Debug for PageTableNode
pub(super) struct PageTableNode<
    // E: PageTableEntryTrait = PageTableEntry,
    // C: PagingConstsTrait = PagingConsts,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
> where
    // [(); C::NR_LEVELS as usize]:,
{
    page: Frame<PageTablePageMeta<E, C>>,
}

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
// #[derive(Debug)] // TODO: Debug for PageTablePageMeta
pub(in crate::mm) struct PageTablePageMeta<
    // E: PageTableEntryTrait = PageTableEntry,
    // C: PagingConstsTrait = PagingConsts,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
> where
    // [(); C::NR_LEVELS as usize]:,
{
    /// The lock for the page table page.
    // TODO: Implement lock for PageTablePageMeta
    // lock: Frame<()>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// Whether the pages mapped by the node is tracked.
    pub is_tracked: MapTrackingStatus,
    _phantom: core::marker::PhantomData<(E, C)>,
}

/// Describe if the physical address recorded in this page table refers to a
/// page tracked by metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(in crate::mm) enum MapTrackingStatus {
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
    pub fn new_locked(
        level: PagingLevel,
        is_tracked: MapTrackingStatus,
        lock_range: Range<usize>,
    ) -> Self {
        // let lock = FrameAllocOptions::new()
        //     .zeroed(false)
        //     .alloc_frame()
        //     .unwrap();
        // let frame_ptr = paddr_to_vaddr(lock.start_paddr()) as *mut (LockBody, u32);

        // for idx in 0..nr_subpage_per_huge::<C>() {
        //     if lock_range.contains(&idx) {
        //         unsafe { frame_ptr.add(idx).write((LockBody::new_locked(), 0)) };
        //     } else {
        //         unsafe { frame_ptr.add(idx).write((LockBody::new(), 0)) };
        //     }
        // }

        // core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

        // Self {
        //     level,
        //     lock,
        //     is_tracked,
        //     _phantom: PhantomData,
        // }
        Self {
            level,
            // lock,
            is_tracked,
            _phantom: PhantomData,
        }
    }

    pub(super) fn lock(&self, idx: usize) {
        // let frame_ptr = paddr_to_vaddr(self.lock.start_paddr()) as *mut (LockBody, u32);
        // let (lock, _) = unsafe { &*frame_ptr.add(idx) };
        // unsafe { lock.lock() };
    }

    pub(super) fn unlock(&self, idx: usize) {
        // let frame_ptr = paddr_to_vaddr(self.lock.start_paddr()) as *mut (LockBody, u32);
        // let (lock, _) = unsafe { &*frame_ptr.add(idx) };
        // unsafe { lock.unlock() };
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
