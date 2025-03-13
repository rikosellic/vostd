extern crate vstd_extra;
use vstd::prelude::*;
use aster_common::{
    x86_64::*,
    mm::*,
    page::{meta::*, model::PageUsePermission},
    page_prop::*,
    page_table::*,
    task::*,
    vm_space::*,
};
use core::mem::size_of;
use core::ops::Range;

verus! {

pub proof fn lemma_meta_to_page_bijectivity(paddr: Paddr)
    requires
        paddr % PAGE_SIZE_SPEC() == 0,
        paddr < MAX_PADDR_SPEC(),
    ensures
        paddr == meta_to_page(page_to_meta(paddr)),
{
}

pub proof fn lemma_page_to_meta_bijectivity(vaddr: Vaddr)
    requires
        FRAME_METADATA_RANGE().start <= vaddr && vaddr < FRAME_METADATA_RANGE().end,
        vaddr % META_SLOT_SIZE() == 0,
    ensures
        vaddr == page_to_meta(meta_to_page(vaddr)),
{
}

} // verus!
verus! {

pub proof fn lemma_meta_to_page_alignment(meta: Vaddr)
    requires
        meta % META_SLOT_SIZE() == 0,
        FRAME_METADATA_RANGE().start <= meta && meta < FRAME_METADATA_RANGE().start + MAX_NR_PAGES()
            * META_SLOT_SIZE(),
    ensures
        meta_to_page(meta) % PAGE_SIZE_SPEC() == 0,
        meta_to_page(meta) < MAX_PADDR_SPEC(),
{
}

} // verus!
