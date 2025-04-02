pub mod cursor;
pub mod node;
mod zeroed_pt_pool;

use vstd::prelude::*;
use node::*;
use core::fmt::Debug;
use std::{marker::PhantomData, ops::Range};

use crate::helpers::extra_num::lemma_usize_ilog2_to32;

use super::{
    meta::AnyFrameMeta, nr_subpage_per_huge, page_prop::PageProperty, vm_space::Token, Paddr,
    PagingLevel, Vaddr,
};

verus! {

pub trait PageTableEntryTrait:
    Clone + Copy + 
    // Default + 
    Sized + Send + Sync + 'static
    // Debug // TODO: Implement Debug for PageTableEntryTrait
    // + Pod + PodOnce // TODO: Implement Pod and PodOnce for PageTableEntryTrait
{
    /// Create a set of new invalid page table flags that indicates an absent page.
    ///
    /// Note that currently the implementation requires an all zero PTE to be an absent PTE.
    // TODO: Implement
    #[verifier::external_body]
    fn new_absent() -> Self {
        // Self::default()
        unimplemented!()
    }

    /// If the flags are present with valid mappings.
    ///
    /// For PTEs created by [`Self::new_absent`], [`Self::new_token`], this
    /// method should return false. And for PTEs created by [`Self::new_page`]
    /// or [`Self::new_pt`], whatever modified with [`Self::set_prop`] or not,
    /// this method should return true.
    fn is_present(&self) -> bool;

    /// Create a new PTE with the given physical address and flags that map to a page.
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self;

    /// Create a new PTE that map to a child page table.
    fn new_pt(paddr: Paddr) -> Self;

    /// Create a new PTE with the given token value but don't map to anything.
    fn new_token(token: Token) -> Self;

    /// Get the physical address from the PTE.
    /// The physical address recorded in the PTE is either:
    ///  - the physical address of the next level page table;
    ///  - the physical address of the page it maps to;
    ///  - the value of the token.
    fn paddr(&self) -> Paddr;

    fn prop(&self) -> PageProperty;

    /// Set the page property of the PTE.
    ///
    /// This will be only done if the PTE is present. If not, this method will
    /// do nothing.
    fn set_prop(&mut self, prop: PageProperty);

    /// Set the physical address of the PTE.
    ///
    /// This can be done for both present and absent PTEs.
    fn set_paddr(&mut self, paddr: Paddr);

    /// If the PTE maps a page rather than a child page table.
    ///
    /// The level of the page table the entry resides is given since architectures
    /// like amd64 only uses a huge bit in intermediate levels.
    fn is_last(&self, level: PagingLevel) -> bool;

    /// Converts the PTE into its corresponding `usize` value.
    // TODO: Implement as_usize and from_usize
    #[verifier::external_body]
    fn as_usize(self) -> usize {
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        // unsafe { transmute_unchecked(self) }
        // TODO: Implement this function
        unimplemented!()
    }

    /// Converts a usize `pte_raw` into a PTE.
    // TODO: Implement as_usize and from_usize
    #[verifier::external_body]
    fn from_usize(pte_raw: usize) -> Self {
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        // unsafe { transmute_unchecked(pte_raw) }
        // TODO: Implement this function
        unimplemented!()
    }
}

/// A minimal set of constants that determines the paging system.
/// This provides an abstraction over most paging modes in common architectures.
pub trait PagingConstsTrait:
// Clone + Debug + Default + Send + Sync + 'static
{

    spec fn BASE_PAGE_SIZE_SPEC() -> usize;

    // /// The smallest page size.
    // /// This is also the page size at level 1 page tables.
    fn BASE_PAGE_SIZE() -> usize;

    spec fn NR_LEVELS_SPEC() -> PagingLevel;

    // /// The number of levels in the page table.
    // /// The numbering of levels goes from deepest node to the root node. For example,
    // /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    // /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    // /// Table, respectively.
    fn NR_LEVELS() -> PagingLevel;

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

    open spec fn BASE_PAGE_SIZE_SPEC() -> usize {
        4096
    }

    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_SPEC)]
    fn BASE_PAGE_SIZE() -> usize { 4096 }

    open spec fn NR_LEVELS_SPEC() -> PagingLevel {
        4
    }

    #[verifier::when_used_as_spec(NR_LEVELS_SPEC)]
    fn NR_LEVELS() -> PagingLevel { 4 }
    // const ADDRESS_WIDTH: usize = 48;
    // const HIGHEST_TRANSLATION_LEVEL: PagingLevel = 2;
    // const PTE_SIZE: usize = core::mem::size_of::<PageTableEntry>();
}

/// This is a compile-time technique to force the frame developers to distinguish
/// between the kernel global page table instance, process specific user page table
/// instance, and device page table instances.
pub trait PageTableMode: Clone + Debug
//  + 'static
{
    /// The range of virtual addresses that the page table can manage.
    // const VADDR_RANGE: Range<Vaddr>;
    fn VADDR_RANGE() -> Range<Vaddr>;

    /// Check if the given range is covered by the valid virtual address range.
    fn covers(r: &Range<Vaddr>) -> bool {
        Self::VADDR_RANGE().start <= r.start && r.end <= Self::VADDR_RANGE().end
    }
}

#[derive(Clone, Debug)]
pub struct UserMode {}

impl PageTableMode for UserMode {
    // const VADDR_RANGE: Range<Vaddr> = 0..super::MAX_USERSPACE_VADDR;
    fn VADDR_RANGE() -> Range<Vaddr> {
        0..super::MAX_USERSPACE_VADDR
    }
}

#[derive(Clone, Debug)]
pub struct KernelMode {}

impl PageTableMode for KernelMode {
    // const VADDR_RANGE: Range<Vaddr> = super::KERNEL_VADDR_RANGE;
    fn VADDR_RANGE() -> Range<Vaddr> {
        super::KERNEL_VADDR_RANGE
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PageTableError {
    /// The provided virtual address range is invalid.
    InvalidVaddrRange(Vaddr, Vaddr),
    /// The provided virtual address is invalid.
    InvalidVaddr(Vaddr),
    /// Using virtual address not aligned.
    UnalignedVaddr,
}

// Copied from aster_common
// TODO: Check if these are correct

// Here are some const values that are determined by the paging constants.
pub proof fn bits_of_base_page_size()
    ensures
        PagingConsts::BASE_PAGE_SIZE_SPEC().ilog2() == 12,
{
    lemma_usize_ilog2_to32();
}

pub proof fn value_of_nr_subpage_per_huge()
    ensures
        // nr_subpage_per_huge::<PagingConsts>() == 512, // TODO
        nr_subpage_per_huge() == 512,
{ }

pub proof fn bits_of_nr_pte_index()
    ensures
        nr_pte_index_bits::<PagingConsts>() == 9,
{
    value_of_nr_subpage_per_huge();
    lemma_usize_ilog2_to32();
}

#[verifier::inline]
pub open spec fn nr_pte_index_bits_spec<C: PagingConstsTrait>() -> usize
{
    // nr_subpage_per_huge::<C>().ilog2() as usize // TODO
    nr_subpage_per_huge().ilog2() as usize
}

/// The number of virtual address bits used to index a PTE in a page.
#[inline(always)]
#[verifier::when_used_as_spec(nr_pte_index_bits_spec)]
pub const fn nr_pte_index_bits<C: PagingConstsTrait>() -> (res: usize)
ensures
    res == nr_pte_index_bits_spec::<C>(),
{
    // nr_subpage_per_huge::<C>().ilog2() as usize // TODO
    nr_subpage_per_huge().ilog2() as usize
}

#[verifier::inline]
pub open spec fn pte_index_mask_spec() -> usize
{
    0x1ff
}

#[inline(always)]
#[verifier::when_used_as_spec(pte_index_mask_spec)]
pub fn pte_index_mask() -> (res: usize)
    ensures
        res == pte_index_mask_spec(),
{
    // nr_subpage_per_huge::<PagingConsts>() - 1 // TODO
    nr_subpage_per_huge() - 1
}

pub open spec fn pte_index_spec(va: Vaddr, level: PagingLevel) -> usize
    recommends
        0 < level <= PagingConsts::NR_LEVELS_SPEC(),
{
    let base_bits = PagingConsts::BASE_PAGE_SIZE_SPEC().ilog2();
    let index_bits = nr_pte_index_bits::<PagingConsts>();
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    (va >> shift) & pte_index_mask()
}

#[verifier::when_used_as_spec(pte_index_spec)]
/// The index of a VA's PTE in a page table node at the given level.
// const fn pte_index<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> usize
pub fn pte_index(va: Vaddr, level: PagingLevel) -> (res: usize) // TODO: type, const
requires
    0 < level <= PagingConsts::NR_LEVELS_SPEC(),
ensures
    res == pte_index_spec(va, level),
{
    let base_bits = PagingConsts::BASE_PAGE_SIZE().ilog2();
    assert(base_bits == 12) by {
        bits_of_base_page_size();
    };
    let index_bits = nr_pte_index_bits::<PagingConsts>();
    assert(index_bits == 9) by {
        bits_of_nr_pte_index();
    };
    assert(0 <= (level - 1) * index_bits <= 36);
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    (va >> shift) & pte_index_mask()
}

pub proof fn pte_index_preserves_order(va1: Vaddr, va2: Vaddr, level: PagingLevel)
    requires
        va1 <= va2
    ensures
        pte_index(va1, level) <= pte_index(va2, level)
{
    // TODO: Implement this proof
    admit()
}

/// A handle to a page table.
/// A page table can track the lifetime of the mapped physical pages.
// TODO: Debug for PageTable
// #[derive(Debug)]
pub struct PageTable<
    M: PageTableMode,
    // E: PageTableEntryTrait = PageTableEntry,
    E: PageTableEntryTrait,
    // C: PagingConstsTrait = PagingConsts,
    C: PagingConstsTrait,
> {
    root: PageTableNode<E, C>,
    _phantom: PhantomData<M>,
}


}
