use vstd::prelude::*;
use vstd::multiset::*;

use super::*;
use super::model::*;
use super::specs::*;
use aster_common::prelude::*;

verus! {

impl PageModel {

#[rustc_allow_incoherent_impl]
pub proof fn lemma_invariant_implies_no_owner(&self)
    requires
        self.invariants(),
        self.state == PageState::Unused
    ensures
        self.usage == PageUsage::Unused,
        self.ref_count == 0,
        self.owners.is_empty()
{}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_invariants_implies_owner(&self)
    requires
        self.invariants(),
        self.state == PageState::Typed || self.state == PageState::Untyped
    ensures
        self.usage != PageUsage::Unused,
        self.ref_count > 0,
        //self.owners.is_empty() == false,
        self.ref_count >= self.owners.len() as int
    {}
}
} // verus!

verus! {

impl PageModel {

#[rustc_allow_incoherent_impl]
pub proof fn insert_keep_owners_invariants(&self, owner: PageOwner)
    requires
        self.owners_invariants(),
        owner.as_usage() == self.usage
    ensures
        forall |owner_| #[trigger]self.owners.insert(owner).contains(owner_) ==> owner_.as_usage() == self.usage
{
    let new_owners = self.owners.insert(owner);
    assert forall |owner_| #[trigger]new_owners.contains(owner_) implies owner_.as_usage() == self.usage by {
        if owner_ == owner {
            assert (owner_.as_usage() == self.usage);
        } else {
            assert (self.owners.contains(owner_));
        }
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn remove_keep_owners_invariants(&self, owner: PageOwner)
    requires
        self.owners_invariants(),
        self.owners.contains(owner)
    ensures
        forall |owner_| #[trigger]self.owners.remove(owner).contains(owner_) ==> owner_.as_usage() == self.usage
{
    let new_owners = self.owners.remove(owner);
    assert forall |owner_| #[trigger]new_owners.contains(owner_) implies owner_.as_usage() == self.usage by {
        assert (self.owners.contains(owner_));
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn transfer_spec_satisfy_invariants(&self, prev_owner: PageOwner, new_owner: PageOwner)
    requires
        self.invariants()
    ensures
        self.transfer_spec(prev_owner, new_owner).is_some() ==>
        self.transfer_spec(prev_owner, new_owner).unwrap().invariants()
{
    if self.transfer_spec(prev_owner, new_owner).is_some() {
        self.lemma_invariants_implies_owner();
        let model = self.transfer_spec(prev_owner, new_owner).unwrap();
        assert forall |owner| #[trigger]model.owners.contains(owner) implies owner.as_usage() == model.usage by {
            if owner == new_owner {
                assert (owner.as_usage() == model.usage);
            } else {
                assert (self.owners.contains(owner));
            }
        }
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn share_with_spec_satisfy_invariants(&self, owner: PageOwner)
    requires
        self.invariants()
    ensures
        self.share_with_spec(owner).is_some() ==>
        self.share_with_spec(owner).unwrap().invariants()
{
    if self.share_with_spec(owner).is_some() {
        self.lemma_invariants_implies_owner();
        let model = self.share_with_spec(owner).unwrap();
        assert forall |owner_| #[trigger]model.owners.contains(owner_) implies owner_.as_usage() == model.usage by {
            if owner_ == owner {
                assert (owner_.as_usage() == model.usage);
            } else {
                assert (self.owners.contains(owner_));
            }
        }
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn drop_spec_satisfy_invariants(&self, owner: PageOwner)
    requires
        self.invariants()
    ensures
        self.drop_spec(owner).is_some() ==>
        self.drop_spec(owner).unwrap().invariants()
{
    if self.drop_spec(owner).is_some() {
        self.lemma_invariants_implies_owner();
        let model = self.drop_spec(owner).unwrap();
        assert forall |owner_| #[trigger]model.owners.contains(owner_) implies owner_.as_usage() == model.usage by {
            assert (self.owners.contains(owner_));
        }
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn leak_owner_spec_satisfy_invariants(&self, owner: PageOwner)
    requires
        self.invariants()
    ensures
        self.leak_owner_spec(owner).is_some() ==>
        self.leak_owner_spec(owner).unwrap().invariants()
{
    if self.leak_owner_spec(owner).is_some() {
        self.lemma_invariants_implies_owner();
        let model = self.leak_owner_spec(owner).unwrap();
        assert forall |owner_| #[trigger]model.owners.contains(owner_) implies owner_.as_usage() == model.usage by {
            assert (self.owners.contains(owner_));
        }
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn leak_owner_spec_isleaked(&self,owner: PageOwner)
    requires
        self.invariants()
    ensures
        self.leak_owner_spec(owner).is_some() ==>
        self.leak_owner_spec(owner).unwrap().isleaked()
{
    assert (self.ref_count >= self.owners.len());
    if self.leak_owner_spec(owner).is_some() {
        let model = self.leak_owner_spec(owner).unwrap();
        assert(self.ref_count == model.ref_count);
        assert(model.owners.len() == self.owners.len() - 1);
    }
}

#[rustc_allow_incoherent_impl]
pub proof fn inc_spec_satisfy_invariants(&self)
    requires
        self.invariants()
    ensures
        self.inc_spec().is_some() ==>
        self.inc_spec().unwrap().invariants()
{}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_leak_owner_then_restore_owner_implies_unchanged(self,owner: PageOwner, middle: PageModel)
    requires
        self.invariants(),
        self.leak_owner_spec(owner) == Some(middle),
    ensures
        middle.restore_owner_spec(owner) == Some(self),
{
    assert(self.owners == self.owners.remove(owner).insert(owner));
}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_leak_owner_then_restore_owner_implies_transfer(self,prev_owner: PageOwner, new_owner: PageOwner, middle: PageModel)
    requires
        self.invariants(),
        self.leak_owner_spec(prev_owner) == Some(middle),
    ensures
        middle.restore_owner_spec(new_owner) == self.transfer_spec(prev_owner, new_owner)
{}

#[rustc_allow_incoherent_impl]
pub proof fn lemma_inc_then_restore_owner_implies_share_with(self,owner: PageOwner, middle: PageModel)
    requires
        self.invariants(),
        !self.owners.is_empty(),
        self.inc_spec() == Some(middle),
        middle.restore_owner_spec(owner).is_some(),
    ensures
        self.share_with_spec(owner) == middle.restore_owner_spec(owner),
{}

}

} // verus!
