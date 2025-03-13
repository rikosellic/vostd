extern crate vstd_extra;
use vstd::prelude::*;
use core::marker::PhantomData;
use aster_common::prelude::*;
use aster_common::x86_64;
use crate::common::*;
use crate::page::{*, model::*};

use super::*;

verus! {

pub const NR_ENTRIES: usize = 512;

pub const NR_LEVELS: usize = 4;

pub const PAGE_SIZE: usize = 4096;

pub const BASE_PAGE_SIZE: usize = 4096;

#[allow(non_snake_case)]
pub proof fn correctness_PAGE_SIZE()
    ensures PAGE_SIZE == mm::PAGE_SIZE(),
{ }

#[allow(non_snake_case)]
pub proof fn correctness_NR_ENTRIES()
    ensures NR_ENTRIES == PAGE_SIZE / PagingConsts::PTE_SIZE(),
{ }

#[allow(non_snake_case)]
pub proof fn correctness_NR_LEVELS()
    ensures NR_LEVELS == mm::NR_LEVELS(),
{ }

#[allow(non_snake_case)]
pub proof fn correctness_BASE_PAGE_SIZE()
    ensures BASE_PAGE_SIZE == x86_64::PagingConsts::BASE_PAGE_SIZE(),
{ }

impl RawPageTableNode{

#[rustc_allow_incoherent_impl]
pub open spec fn relate_model(&self, model: PageModel) -> bool
{
    &&& page_to_index_spec(self.raw as int) == model.index
    &&& model.state == PageState::Typed
    &&& model.usage == PageUsage::PageTable
    &&& model.owners.contains(RAW_PAGE_TABLE_NODE_OWNER)
}

#[rustc_allow_incoherent_impl]
pub open spec fn has_valid_paddr(&self) -> bool
{
    &&& self.raw < MAX_PADDR_SPEC()
    &&& self.raw % PAGE_SIZE_SPEC() == 0
}

}

} //verus!

verus! {

impl PageTableNode{

#[rustc_allow_incoherent_impl]
pub open spec fn relate_model(&self, model: PageModel) -> bool
{
    &&& self.page.relate_model(model)
    &&& model.state == PageState::Typed
    &&& model.usage == PageUsage::PageTable
    &&& model.owners.contains(PAGE_TABLE_NODE_OWNER)
}

#[verifier::inline]
#[rustc_allow_incoherent_impl]
pub open spec fn has_valid_paddr(&self) -> bool
{
    self.page.has_valid_paddr()
}

#[verifier::inline]
#[rustc_allow_incoherent_impl]
pub open spec fn inv_ptr(&self) -> bool
{
    self.page.inv_ptr()
}

}

} //verus!
