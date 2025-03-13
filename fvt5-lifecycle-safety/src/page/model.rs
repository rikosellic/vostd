extern crate vstd_extra;
use vstd::prelude::*;
use vstd::atomic::*;
use vstd::atomic_ghost::*;
use vstd::simple_pptr;
use vstd::cell;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use super::*;
use super::AbstractState;
use aster_common::prelude::*;

verus! {

impl<M: PageMeta> Page<M> {

#[rustc_allow_incoherent_impl]
pub proof fn lemma_inv_ptr_implies_has_valid_paddr(&self)
ensures
    self.inv_ptr() ==> self.has_valid_paddr()
{
    if self.inv_ptr()
    { lemma_meta_to_page_soundness(self.ptr.addr() as Vaddr); }
}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_relate_model_has_valid_index_implies_inv_ptr(&self, model: PageModel)
    requires
        self.relate_model(model),
        model.has_valid_index(),
    ensures
        self.inv_ptr(),
{}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_has_valid_paddr_implies_get_page_satisfies_invariants(&self, s: AbstractState)
    requires
        s.invariants(),
        self.has_valid_paddr(),
    ensures
        s.get_page(self.paddr()).invariants(),
{
    s.lemma_get_page_satisfies_invariants(self.paddr());
}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_has_valid_paddr_implies_get_page_has_valid_index(&self, s: AbstractState)
    requires
        s.invariants(),
        self.has_valid_paddr(),
    ensures
        s.get_page(self.paddr()).has_valid_index(),
{
    s.lemma_get_page_has_valid_index(self.paddr());
}

}//verus!

}

verus! {

impl DynPage{

#[rustc_allow_incoherent_impl]
pub open spec fn has_valid_paddr(self) -> bool {
    &&& self.paddr() < MAX_PADDR_SPEC()
    &&& self.paddr() % PAGE_SIZE_SPEC() == 0
}

#[rustc_allow_incoherent_impl]
pub open spec fn relate_model(&self, model: PageModel) -> bool {
    &&& self.ptr.addr() == FRAME_METADATA_RANGE().start + model.index * META_SLOT_SIZE()
}

}

}

verus! {
//Primitive operations on PageModel in proof mode
impl PageModel {

#[rustc_allow_incoherent_impl]
pub proof fn share_with(&self, owner:PageOwner) -> (res:Self)
    requires
        self.invariants(),
        !self.owners.is_empty(),
        owner.as_usage() == self.usage,
    ensures
    res.invariants(),
    self.share_with_spec(owner) == Some(res),
{
    self.insert_keep_owners_invariants(owner);
    PageModel {
        ref_count: self.ref_count + 1,
        owners: self.owners.insert(owner),
        ..*self
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn leak_owner(&self, owner:PageOwner) -> (res:Self)
    requires
        self.invariants(),
        self.owners.contains(owner),
    ensures
        res.invariants(),
        self.leak_owner_spec(owner) == Some(res),
{
    self.remove_keep_owners_invariants(owner);
    PageModel {
        owners: self.owners.remove(owner),
        ..*self
    }

}

#[rustc_allow_incoherent_impl]
pub proof fn restore_owner(&self, owner:PageOwner) -> (res:Self)
    requires
        self.invariants(),
        self.isleaked(),
        owner.as_usage() == self.usage,
ensures
    res.invariants(),
    self.restore_owner_spec(owner) == Some(res),
{
    self.insert_keep_owners_invariants(owner);
    PageModel {
        owners: self.owners.insert(owner),
        ..*self
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn inc(&self) -> (res:Self)
    requires
        self.invariants(),
        self.usage != PageUsage::Unused,
    ensures
        res.invariants(),
        self.inc_spec() == Some(res),
{
    PageModel {
        ref_count: self.ref_count + 1,
        ..*self
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn transfer(&self, prev_owner:PageOwner, new_owner:PageOwner) -> (res:Self)
    requires
        self.invariants(),
        self.owners.contains(prev_owner),
        new_owner.as_usage() == self.usage,
    ensures
        res.invariants(),
        self.transfer_spec(prev_owner, new_owner) == Some(res),
{
    self.transfer_spec_satisfy_invariants(prev_owner, new_owner);
    PageModel {
        owners: self.owners.remove(prev_owner).insert(new_owner),
        ..*self
    }

}
}

}
