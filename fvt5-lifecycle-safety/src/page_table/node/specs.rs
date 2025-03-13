use vstd::prelude::*;

use core::marker::PhantomData;
use aster_common::prelude::*;

use crate::common::*;
use crate::page::{*, model::*};
use super::*;

verus! {

impl RawPageTableNode{

#[rustc_allow_incoherent_impl]
pub open spec fn inc_ref_count_spec(
    self, s1: AbstractState, s2: AbstractState) -> bool
{
    let paddr = self.paddr();
    let model1 = s1.get_page(paddr);
    let model2 = s2.get_page(paddr);
    {
        &&& self.relate_model(model1)
        //&&& model1.inc_spec() == Some(model2)
        &&& model2.invariants()
        &&& model2.isleaked()
        &&& s2.ghost_eq(s1.inc_at_spec(paddr))
        //&&& s2.ghost_eq(s1.update_page_model_spec(paddr,model2))
    }
}

#[rustc_allow_incoherent_impl]
pub open spec fn lock_spec(
    self, node: PageTableNode, s1: AbstractState, s2: AbstractState) -> bool
{
    let paddr = self.paddr();
    let model1 = s1.get_page(paddr);
    let model2 = s2.get_page(paddr);
    {
        &&& self.relate_model(model1)
        //&&& model1.transfer_spec(RAW_PAGE_TABLE_NODE_OWNER,PAGE_TABLE_NODE_OWNER) == Some(model2)
        &&& node.relate_model(model2)
        &&& model2.invariants()
        &&& s2.ghost_eq(s1.transfer_at_spec(paddr,RAW_PAGE_TABLE_NODE_OWNER,PAGE_TABLE_NODE_OWNER))
    }
}

#[rustc_allow_incoherent_impl]
pub open spec fn clone_shallow_spec(
    self, s1: AbstractState, s2: AbstractState) -> bool
{
    let paddr = self.paddr();
    let model1 = s1.get_page(paddr);
    let model2 = s2.get_page(paddr);
    {
        &&& self.relate_model(model1)
        //&&& model1.share_with_spec(RAW_PAGE_TABLE_NODE_OWNER) == Some(model2)
        &&& model2.invariants()
        &&& s2.ghost_eq(s1.share_with_at_spec(paddr,RAW_PAGE_TABLE_NODE_OWNER))
        //&&& s2.ghost_eq(s1.update_page_model_spec(paddr,model2))
    }
}

#[rustc_allow_incoherent_impl]
pub open spec fn from_raw_parts_spec(
    paddr:Paddr, s1: AbstractState, s2: AbstractState) -> bool
{
    let model1 = s1.get_page(paddr);
    let model2 = s2.get_page(paddr);
    {
        &&& model1.isleaked()
        //&&& model1.restore_owner_spec(RAW_PAGE_TABLE_NODE_OWNER) == Some(model2)
        &&& model2.invariants()
        &&& s2.ghost_eq(s1.restore_owner_at_spec(paddr,RAW_PAGE_TABLE_NODE_OWNER))
        //&&& s2.ghost_eq(s1.update_page_model_spec(paddr,model2))
    }
}

#[rustc_allow_incoherent_impl]
pub open spec fn first_activate_spec(
    self, s1: AbstractState, s2: AbstractState) -> bool
{
    let paddr = self.paddr();
    let model1 = s1.get_page(paddr);
    {
        &&& self.relate_model(model1)
        &&& s2.ghost_eq(s1.share_with_at_spec(paddr,PAGE_TABLE_CPU_OWNER))
    }
}
}


impl PageTableNode{

#[rustc_allow_incoherent_impl]
pub open spec fn clone_raw_spec(
    &self, s1: AbstractState, s2: AbstractState) -> bool
{
    let paddr = self.paddr();
    let model1 = s1.get_page(paddr);
    let model2 = s2.get_page(paddr);
    {
        &&& self.relate_model(model1)
        //&&& model1.share_with_spec(RAW_PAGE_TABLE_NODE_OWNER) == Some(model2)
        &&& model2.invariants()
        &&& s2.ghost_eq(s1.share_with_at_spec(paddr,RAW_PAGE_TABLE_NODE_OWNER))
        //&&& s2.ghost_eq(s1.update_page_model_spec(paddr,model2))
    }
}

#[rustc_allow_incoherent_impl]
pub open spec fn into_raw_spec(
    self, s1: AbstractState, s2: AbstractState) -> bool
{
    let paddr = self.paddr();
    let model1 = s1.get_page(paddr);
    let model2 = s2.get_page(paddr);
    {
        &&& self.relate_model(model1)
        &&& model2.invariants()
        &&& s2.ghost_eq(s1.transfer_at_spec(paddr,PAGE_TABLE_NODE_OWNER,RAW_PAGE_TABLE_NODE_OWNER))
    }
}
}

} //verus!
