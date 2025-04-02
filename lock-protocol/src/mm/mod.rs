pub mod page_table;
pub mod frame;
pub(crate) mod page_prop;
pub mod vm_space;

use std::ops::Range;

use vstd::prelude::*;
pub use page_table::*;
pub use page_table::node::*;
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
pub(crate) const fn page_size<C: PagingConstsTrait>(level: PagingLevel) -> usize {
    // C::BASE_PAGE_SIZE << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
    BASE_PAGE_SIZE << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
}

/// The number of sub pages in a huge page.
pub(crate) const fn nr_subpage_per_huge<C: PagingConstsTrait>() -> usize {
    // C::BASE_PAGE_SIZE / C::PTE_SIZE
    BASE_PAGE_SIZE / PTE_SIZE
}

/// The maximum virtual address of user space (non inclusive).
///
/// Typical 64-bit systems have at least 48-bit virtual address space.
/// A typical way to reserve half of the address space for the kernel is
/// to use the highest 48-bit virtual address space.
///
/// Also, the top page is not regarded as usable since it's a workaround
/// for some x86_64 CPUs' bugs. See
/// <https://github.com/torvalds/linux/blob/480e035fc4c714fb5536e64ab9db04fedc89e910/arch/x86/include/asm/page_64.h#L68-L78>
/// for the rationale.
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000 - PAGE_SIZE;

/// The kernel address space.
///
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> = 0xffff_8000_0000_0000..0xffff_ffff_ffff_0000;

} // verus!