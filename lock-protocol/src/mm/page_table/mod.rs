pub mod node;

use vstd::prelude::*;
use node::*;
use core::fmt::Debug;

verus! {

pub trait PageTableEntryTrait:
    // Clone + Copy + Default + Sized + Send + Sync + 'static
    // Debug // TODO: Implement Debug for PageTableEntryTrait
    // + Pod + PodOnce // TODO: Implement Pod and PodOnce for PageTableEntryTrait
{
    // TODO: PageTableEntryTrait
}


// #[derive(Clone, Copy, Pod, Default)]
// TODO: What is Pod and PodOnce?
// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
// #[derive(Clone, Copy, Default)]
// #[repr(C)] // TODO: repr(C)
pub struct PageTableEntry(usize);


// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
// TODO: implement PageTableEntryTrait for PageTableEntry
impl PageTableEntryTrait for PageTableEntry {}

pub type PagingLevel = u8;

/// A minimal set of constants that determines the paging system.
/// This provides an abstraction over most paging modes in common architectures.
pub(crate) trait PagingConstsTrait:
    // Clone + Debug + Default + Send + Sync + 'static
    {
    // /// The smallest page size.
    // /// This is also the page size at level 1 page tables.
    // const BASE_PAGE_SIZE: usize;

    // /// The number of levels in the page table.
    // /// The numbering of levels goes from deepest node to the root node. For example,
    // /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    // /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    // /// Table, respectively.
    // const NR_LEVELS: PagingLevel;

    // /// The highest level that a PTE can be directly used to translate a VA.
    // /// This affects the the largest page size supported by the page table.
    // const HIGHEST_TRANSLATION_LEVEL: PagingLevel;

    // /// The size of a PTE.
    // const PTE_SIZE: usize;

    // /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    // /// If it is shorter than that, the higher bits in the highest level are ignored.
    // const ADDRESS_WIDTH: usize;
}

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
pub(crate) const NR_ENTRIES_PER_PAGE: usize = 512;

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
// #[derive(Clone, Debug, Default)]
pub struct PagingConsts {}

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
impl PagingConstsTrait for PagingConsts {
    // const BASE_PAGE_SIZE: usize = 4096;
    // const NR_LEVELS: PagingLevel = 4;
    // const ADDRESS_WIDTH: usize = 48;
    // const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 2;
    // const PTE_SIZE: usize = core::mem::size_of::<PageTableEntry>();
}

}
