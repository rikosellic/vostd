pub mod page_table;
pub mod frame;

use vstd::prelude::*;
pub use page_table::*;
pub use frame::*;

verus! {

/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

// TODO: Formalize these constants
pub const NR_ENTRIES: usize = 512;
pub const NR_LEVELS: usize = 4;
pub const PAGE_SIZE: usize = 4096;
pub const BASE_PAGE_SIZE: usize = 4096;
pub const PTE_SIZE: usize = 8;

/// The page size
// pub const PAGE_SIZE: usize = page_size::<PagingConsts>(1);

/// The page size at a given level.
// TODO: Formalize page_size
// pub(crate) const fn page_size<C: PagingConstsTrait>(level: PagingLevel) -> usize {
//     // C::BASE_PAGE_SIZE << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
//     BASE_PAGE_SIZE << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
// }

/// The number of sub pages in a huge page.
pub(crate) const fn nr_subpage_per_huge<C: PagingConstsTrait>() -> usize {
    // C::BASE_PAGE_SIZE / C::PTE_SIZE
    BASE_PAGE_SIZE / PTE_SIZE
}

} // verus!