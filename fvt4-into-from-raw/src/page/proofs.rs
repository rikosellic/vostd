use vstd::prelude::*;
use vstd::set::*;

use crate::common::MAX_NR_PAGES;
use super::*;
use super::model::*;
use super::specs::*;

verus! {

pub proof fn lemma_empty_set_contains_nothing<T>(x: T)
    ensures
        Set::<T>::empty().contains(x) == false,
{
}

pub proof fn lemma_empty_set_is_empty<T>(set: Set<T>)
    requires
        set.finite(),
        set.is_empty(),
    ensures
        set =~= Set::<T>::empty(),
{
}

pub proof fn lemma_set_is_empty_contains_nothing<T>(set: Set<T>, x: T)
    requires
        set.finite(),
        set.is_empty(),
    ensures
        set.contains(x) == false,
{
    lemma_empty_set_is_empty(set);
    lemma_empty_set_contains_nothing(x);
}

} // verus!
verus! {

impl PageModel {
    pub proof fn lemma_invariants_implies_no_owner(&self)
        requires
            self.invariants(),
            self.state == PageState::Unused,
        ensures
            self.usage == PageUsage::Unused,
            self.ref_count == 0,
            self.owners.is_empty(),
    {
    }

    pub proof fn lemma_invariants_implies_owner(&self)
        requires
            self.invariants(),
            self.state == PageState::Typed || self.state == PageState::Untyped,
        ensures
            self.usage != PageUsage::Unused,
            self.ref_count > 0,
            self.owners.is_empty() == false,
            self.ref_count >= self.owners.len() as int,
    {
    }

    pub proof fn relate_meta_slot_implies_relate_model(
        &self,
        slot: &MetaSlot,
        model: &MetaSlotModel,
    )
        requires
            slot.inv_relate(model),
            self.relate_meta_slot(slot),
        ensures
            self.index * PAGE_SIZE == model.address@,
    {
        assert(model.address@ == meta_to_page(slot.id())) by {
            assert(slot.inv_relate(model));
        }
        assert(slot.id() == FRAME_METADATA_RANGE.start + model.address@ / 256);
        assert(slot.id() == FRAME_METADATA_RANGE.start + self.index * META_SLOT_SIZE) by {
            assert(self.relate_meta_slot(slot));
        }
        assert(model.address@ / 256 == self.index * META_SLOT_SIZE);
        assert(model.address@ == self.index * PAGE_SIZE);
    }
}

} // verus!
verus! {

impl PageModel {
    pub proof fn new_spec_satisfy_invariants(&self, usage: PageUsage, owner: PageOwner)
        requires
            self.invariants(),
        ensures
            self.new_spec(usage, owner).is_some() ==> self.new_spec(
                usage,
                owner,
            ).unwrap().invariants(),
    {
    }

    pub proof fn transfer_spec_satisfy_invariants(&self, prevOwner: PageOwner, newOwner: PageOwner)
        requires
            self.invariants(),
        ensures
            self.transfer_spec(prevOwner, newOwner).is_some() ==> self.transfer_spec(
                prevOwner,
                newOwner,
            ).unwrap().invariants(),
    {
        if self.state == PageState::Unused {
            assert(self.owners.is_empty());
            assert(self.owners.contains(prevOwner) == false);
            assert(self.transfer_spec(prevOwner, newOwner).is_some() == false);
        } else {
            self.lemma_invariants_implies_owner();
        }
    }

    pub proof fn share_with_spec_satisfy_invariants(&self, owner: PageOwner)
        requires
            self.invariants(),
        ensures
            self.share_with_spec(owner).is_some() ==> self.share_with_spec(
                owner,
            ).unwrap().invariants(),
    {
        if self.state == PageState::Unused {
            assert(self.owners.is_empty());
            assert(self.share_with_spec(owner).is_some() == false);
        } else {
            self.lemma_invariants_implies_owner();
        }
    }

    pub proof fn drop_spec_satisfy_invariants(&self, owner: PageOwner)
        requires
            self.invariants(),
        ensures
            self.drop_spec(owner).is_some() ==> self.drop_spec(owner).unwrap().invariants(),
    {
        if self.state == PageState::Unused {
            assert(self.owners.is_empty());
            assert(self.owners.contains(owner) == false);
            assert(self.drop_spec(owner).is_some() == false);
        } else {
            self.lemma_invariants_implies_owner();
        }
    }
}

} // verus!
