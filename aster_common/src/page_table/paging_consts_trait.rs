use vstd::layout::is_power_2;
use vstd::prelude::*;

use crate::prelude::*;
use core::fmt::Debug;
use core::ops::Range;

use vstd_extra::extern_const;

verus! {

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
extern_const!(pub MAX_NR_LEVELS [MAX_NR_LEVELS_SPEC, CONST_MAX_NR_LEVELS]: usize = 4);

#[allow(non_snake_case)]
pub trait PagingConstsTrait: Debug + Sync {
    spec fn BASE_PAGE_SIZE_spec() -> usize;

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_power_2(Self::BASE_PAGE_SIZE_spec() as int),
    ;

    /// The smallest page size.
    /// This is also the page size at level 1 page tables.
    #[inline(always)]
    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_spec)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        ensures
            res == Self::BASE_PAGE_SIZE_spec(),
            0 < res,
            is_power_2(res as int),
    ;

    spec fn NR_LEVELS_spec() -> PagingLevel;

    /// The number of levels in the page table.
    /// The numbering of levels goes from deepest node to the root node. For example,
    /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    /// Table, respectively.
    #[inline(always)]
    #[verifier::when_used_as_spec(NR_LEVELS_spec)]
    fn NR_LEVELS() -> (res: PagingLevel)
        ensures
            res == NR_LEVELS(),
            res == Self::NR_LEVELS_spec(),
            res > 0,
    ;

    spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel;

    /// The highest level that a PTE can be directly used to translate a VA.
    /// This affects the the largest page size supported by the page table.
    #[inline(always)]
    #[verifier::when_used_as_spec(HIGHEST_TRANSLATION_LEVEL_spec)]
    fn HIGHEST_TRANSLATION_LEVEL() -> (res: PagingLevel)
        ensures
            res == Self::HIGHEST_TRANSLATION_LEVEL_spec(),
    ;

    spec fn PTE_SIZE_spec() -> usize;

    /// The size of a PTE.
    #[inline(always)]
    #[verifier::when_used_as_spec(PTE_SIZE_spec)]
    fn PTE_SIZE() -> (res: usize)
        ensures
            res == Self::PTE_SIZE_spec(),
            is_power_2(res as int),
            0 < res <= Self::BASE_PAGE_SIZE(),
    ;

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_power_2(Self::PTE_SIZE_spec() as int),
    ;

    spec fn ADDRESS_WIDTH_spec() -> usize;

    /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    /// If it is shorter than that, the higher bits in the highest level are ignored.
    #[inline(always)]
    #[verifier::when_used_as_spec(ADDRESS_WIDTH_spec)]
    fn ADDRESS_WIDTH() -> (res: usize)
        ensures
            res == Self::ADDRESS_WIDTH_spec(),
    ;

    /// Whether virtual addresses are sign-extended.
    ///
    /// The sign bit of a [`Vaddr`] is the bit at index [`PagingConstsTrait::ADDRESS_WIDTH`] - 1.
    /// If this constant is `true`, bits in [`Vaddr`] that are higher than the sign bit must be
    /// equal to the sign bit. If an address violates this rule, both the hardware and OSTD
    /// should reject it.
    ///
    /// Otherwise, if this constant is `false`, higher bits must be zero.
    ///
    /// Regardless of sign extension, [`Vaddr`] is always not signed upon calculation.
    /// That means, `0xffff_ffff_ffff_0000 < 0xffff_ffff_ffff_0001` is `true`.
    spec fn VA_SIGN_EXT_spec() -> bool;

    #[inline(always)]
    #[verifier::when_used_as_spec(VA_SIGN_EXT_spec)]
    fn VA_SIGN_EXT() -> bool;

}

/// The configurations of a page table.
///
/// It abstracts away both the usage and the architecture specifics from the
/// general page table implementation. For examples:
///  - the managed virtual address range;
///  - the trackedness of physical mappings;
///  - the PTE layout;
///  - the number of page table levels, etc.
///
/// # Safety
///
/// The implementor must ensure that the `item_into_raw` and `item_from_raw`
/// are implemented correctly so that:
///  - `item_into_raw` consumes the ownership of the item;
///  - if the provided raw form matches the item that was consumed by
///    `item_into_raw`, `item_from_raw` restores the exact item that was
///    consumed by `item_into_raw`.
pub unsafe trait PageTableConfig:
    Clone + Debug + Send + Sync + 'static
{
    /// The index range at the top level (`C::NR_LEVELS`) page table.
    ///
    /// When configured with this value, the [`PageTable`] instance will only
    /// be allowed to manage the virtual address range that is covered by
    /// this range. The range can be smaller than the actual allowed range
    /// specified by the hardware MMU (limited by `C::ADDRESS_WIDTH`).
    spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize>;
    fn TOP_LEVEL_INDEX_RANGE() -> (r: Range<usize>)
        ensures
            r == Self::TOP_LEVEL_INDEX_RANGE_spec();

    /// If we can remove the top-level page table entries.
    ///
    /// This is for the kernel page table, whose second-top-level page
    /// tables need `'static` lifetime to be shared with user page tables.
    /// Other page tables do not need to set this to `false`.
    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        true
    }
    fn TOP_LEVEL_CAN_UNMAP() -> (b:bool)
        ensures
            b == Self::TOP_LEVEL_CAN_UNMAP_spec();

    /// The type of the page table entry.
    type E: PageTableEntryTrait;

    /// The paging constants.
    type C: PagingConstsTrait;

    /// The item that can be mapped into the virtual memory space using the
    /// page table.
    ///
    /// Usually, this item is a [`crate::mm::Frame`], which we call a "tracked"
    /// frame. The page table can also do "untracked" mappings that only maps
    /// to certain physical addresses without tracking the ownership of the
    /// mapped physical frame. The user of the page table APIs can choose by
    /// defining this type and the corresponding methods [`item_into_raw`] and
    /// [`item_from_raw`].
    ///
    /// [`item_from_raw`]: PageTableConfig::item_from_raw
    /// [`item_into_raw`]: PageTableConfig::item_into_raw
    type Item: Clone;

    /// Consumes the item and returns the physical address, the paging level,
    /// and the page property.
    ///
    /// The ownership of the item will be consumed, i.e., the item will be
    /// forgotten after this function is called.
    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

    /// Restores the item from the physical address and the paging level.
    ///
    /// There could be transformations after [`PageTableConfig::item_into_raw`]
    /// and before [`PageTableConfig::item_from_raw`], which include:
    ///  - splitting and coalescing the items, for example, splitting one item
    ///    into 512 `level - 1` items with and contiguous physical addresses;
    ///  - protecting the items, for example, changing the page property.
    ///
    /// Splitting and coalescing maintains ownership rules, i.e., if one
    /// physical address is within the range of one item, after splitting/
    /// coalescing, there should be exactly one item that contains the address.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  - the physical address and the paging level represent a page table
    ///    item or part of it (as described above);
    ///  - either the ownership of the item is properly transferred to the
    ///    return value, or the return value is wrapped in a
    ///    [`core::mem::ManuallyDrop`] that won't outlive the original item.
    ///
    /// A concrete trait implementation may require the caller to ensure that
    ///  - the [`super::PageFlags::AVAIL1`] flag is the same as that returned
    ///    from [`PageTableConfig::item_into_raw`].
    unsafe fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item;
}

// Implement it so that we can comfortably use low level functions
// like `page_size::<C>` without typing `C::C` everywhere.
impl<C: PageTableConfig> PagingConstsTrait for C {
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        C::C::BASE_PAGE_SIZE_spec()
    }

    fn BASE_PAGE_SIZE() -> usize {
        C::C::BASE_PAGE_SIZE()
    }
    
    open spec fn NR_LEVELS_spec() -> PagingLevel {
        C::C::NR_LEVELS_spec()
    }
    fn NR_LEVELS() -> PagingLevel {
        C::C::NR_LEVELS()
    }

    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL_spec()
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL()
    }

    open spec fn PTE_SIZE_spec() -> usize {
        C::C::PTE_SIZE_spec()
    }

    fn PTE_SIZE() -> usize {
        C::C::PTE_SIZE()
    }

    open spec fn ADDRESS_WIDTH_spec() -> usize {
        C::C::ADDRESS_WIDTH_spec()
    } 

    fn ADDRESS_WIDTH() -> usize {
        C::C::ADDRESS_WIDTH()
    } 

    open spec fn VA_SIGN_EXT_spec() -> bool {
        C::C::VA_SIGN_EXT_spec()
    }

    fn VA_SIGN_EXT() -> bool {
        C::C::VA_SIGN_EXT()
    }

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_power_2(Self::BASE_PAGE_SIZE_spec() as int),
    { admit() }

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_power_2(Self::PTE_SIZE_spec() as int),
    { admit() }
}


} // verus!
