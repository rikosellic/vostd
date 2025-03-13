extern crate vstd_extra;
use vstd::prelude::*;

use super::page::model::*;
use super::common::*;

use aster_common::prelude::*;

verus! {

impl AbstractState {
    #[rustc_allow_incoherent_impl]
    pub open spec fn remove_pageperm_spec(self, paddr: Paddr) -> AbstractState
        recommends
            self.perms.dom().contains(page_to_index_spec(paddr as int)),
    {
        let index = page_to_index_spec(paddr as int);
        AbstractState { perms: self.perms.remove(index), ..self }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn insert_pageperm_spec(self, paddr: Paddr, perm: PagePerm) -> AbstractState
        recommends
            !self.perms.dom().contains(page_to_index_spec(paddr as int)),
            self.pages[page_to_index_spec(paddr as int)].relate_perm(perm),
    {
        let index = page_to_index_spec(paddr as int);
        AbstractState { perms: self.perms.insert(index, perm), ..self }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn leak_owner_at_spec(self, paddr: Paddr, owner: PageOwner) -> AbstractState
        recommends
            self.get_page(paddr).owners.contains(owner),
    {
        let page_model = self.get_page(paddr);
        let leaked_model = page_model.leak_owner_spec(owner).unwrap();
        self.update_page_model_spec(paddr, leaked_model)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn restore_owner_at_spec(self, paddr: Paddr, owner: PageOwner) -> AbstractState
        recommends
            self.get_page(paddr).isleaked(),
            owner.as_usage() == self.get_page(paddr).usage,
    {
        let page_model = self.get_page(paddr);
        let restored_model = page_model.restore_owner_spec(owner).unwrap();
        self.update_page_model_spec(paddr, restored_model)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inc_at_spec(self, paddr: Paddr) -> AbstractState
        recommends
            self.get_page(paddr).usage != PageUsage::Unused,
    {
        let page_model = self.get_page(paddr);
        let inc_model = page_model.inc_spec().unwrap();
        self.update_page_model_spec(paddr, inc_model)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn share_with_at_spec(self, paddr: Paddr, owner: PageOwner) -> AbstractState
        recommends
            owner.as_usage() == self.get_page(paddr).usage,
    {
        let page_model = self.get_page(paddr);
        let shared_model = page_model.share_with_spec(owner).unwrap();
        self.update_page_model_spec(paddr, shared_model)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn transfer_at_spec(
        &self,
        paddr: Paddr,
        prev_owner: PageOwner,
        new_owner: PageOwner,
    ) -> AbstractState
        recommends
            self.get_page(paddr).owners.contains(prev_owner),
    {
        let page_model = self.get_page(paddr);
        let transferred_model = page_model.transfer_spec(prev_owner, new_owner).unwrap();
        self.update_page_model_spec(paddr, transferred_model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn get_page_ghost(&self, paddr: Paddr) -> (res: PageModel)
        requires
            self.pages_invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            res == self.get_page(paddr),
            res.invariants(),
            res.index == page_to_index_spec(paddr as int),
    {
        let idx = page_to_index(paddr);
        assert(self.pages.dom().contains(idx));
        self.pages[idx]
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn take_pageperm(tracked &mut self, paddr: Paddr) -> (tracked perm: PagePerm)
        requires
            old(self).perms_invariants(),
            old(self).invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            self == Self::remove_pageperm_spec(*old(self), paddr),
            perm == old(self).perms[page_to_index_spec(paddr as int)],
            self.pages[page_to_index_spec(paddr as int)].relate_perm(perm),
            perm.invariants(),
            self.invariants(),
    {
        let index = page_to_index_spec(paddr as int);
        assert(self.perms.dom().contains(index));
        let tracked res = self.perms.tracked_remove(index);
        assert(self.invariants()) by { admit() };
        res
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn insert_pageperm(tracked &mut self, paddr: Paddr, tracked perm: PagePerm)
        requires
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            old(self).invariants(),
        ensures
            self == Self::insert_pageperm_spec(*old(self), paddr, perm),
            self.invariants(),
    {
        let index = page_to_index_spec(paddr as int);
        self.perms.tracked_insert(index, perm);
        assert(self.invariants()) by { admit() };
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn borrow_pageperm(tracked &self, paddr: Paddr) -> (tracked res: &PagePerm)
        requires
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.perms.dom().contains(page_to_index_spec(paddr as int)),
            self.perms_invariants(),
        ensures
            res == self.perms[page_to_index_spec(paddr as int)],
            self.pages[page_to_index_spec(paddr as int)].relate_perm(*res),
            res.invariants(),
    {
        let index = page_to_index_spec(paddr as int);
        self.perms.tracked_borrow(index)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn update_page_model_tracked(
        tracked self,
        paddr: Paddr,
        model: PageModel,
    ) -> (tracked res: AbstractState)
        requires
            self.invariants(),
            model.index == page_to_index_spec(paddr as int),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            res == self.update_page_model_spec(paddr, model),
            res.invariants(),
    {
        let index = page_to_index(paddr);
        let tracked res = AbstractState { pages: self.pages.insert(index, model), ..self };
        assert(res.invariants()) by { admit() };
        res
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn leak_owner_at(tracked self, paddr: Paddr, owner: PageOwner) -> (tracked res:
        AbstractState)
        requires
            self.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.get_page(paddr).owners.contains(owner),
        ensures
            self.get_page(paddr).leak_owner_spec(owner).is_some(),
            self.get_page(paddr).leak_owner_spec(owner).unwrap().invariants(),
            self.get_page(paddr).leak_owner_spec(owner).unwrap().isleaked(),
            res == self.leak_owner_at_spec(paddr, owner),
            res.invariants(),
    {
        let page_model = self.get_page_ghost(paddr);
        let leaked_model = page_model.leak_owner(owner);
        self.lemma_get_page_implies_relate_perm(paddr);
        self.lemma_update_page_model_spec_model_relate_perm_keeps_perms_invariants(
            paddr,
            leaked_model,
        );
        self.update_page_model_tracked(paddr, leaked_model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn restore_owner_at(tracked self, paddr: Paddr, owner: PageOwner) -> (tracked res:
        AbstractState)
        requires
            self.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.get_page(paddr).isleaked(),
            owner.as_usage() == self.get_page(paddr).usage,
        ensures
            self.get_page(paddr).restore_owner_spec(owner).is_some(),
            self.get_page(paddr).restore_owner_spec(owner).unwrap().invariants(),
            res == self.restore_owner_at_spec(paddr, owner),
            res.invariants(),
    {
        let page_model = self.get_page_ghost(paddr);
        let restored_model = page_model.restore_owner(owner);
        self.lemma_get_page_implies_relate_perm(paddr);
        self.lemma_update_page_model_spec_model_relate_perm_keeps_perms_invariants(
            paddr,
            restored_model,
        );
        self.update_page_model_tracked(paddr, restored_model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn inc_at(
        tracked self,
        paddr: Paddr,
        tracked perm: PagePerm,
        init_state: AbstractState,
    ) -> (tracked res: AbstractState)
        requires
            init_state.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            perm.invariants(),
            self.invariants(),
            self == init_state.remove_pageperm_spec(paddr),
            self.get_page(paddr).usage != PageUsage::Unused,
            self.get_page(paddr).inc_spec().unwrap().relate_perm(perm),
        ensures
            self.get_page(paddr).inc_spec().is_some(),
            self.get_page(paddr).inc_spec().unwrap().invariants(),
            res.ghost_eq(self.inc_at_spec(paddr)),
            res.invariants(),
    {
        let tracked mut s = self;
        let page_model = self.get_page_ghost(paddr);
        let inc_model = page_model.inc();
        s.lemma_update_page_model_spec_with_insert_pageperm_implies_invariants(
            paddr,
            inc_model,
            init_state,
            &perm,
        );
        s.insert_pageperm(paddr, perm);
        s.update_page_model_tracked(paddr, inc_model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn share_with_at(
        tracked self,
        paddr: Paddr,
        owner: PageOwner,
        tracked perm: PagePerm,
        init_state: AbstractState,
    ) -> (tracked res: AbstractState)
        requires
            init_state.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            perm.invariants(),
            self == init_state.remove_pageperm_spec(paddr),
            self.invariants(),
            !self.get_page(paddr).owners.is_empty(),
            owner.as_usage() == self.get_page(paddr).usage,
            self.get_page(paddr).share_with_spec(owner).unwrap().relate_perm(perm),
        ensures
            self.get_page(paddr).share_with_spec(owner).is_some(),
            self.get_page(paddr).share_with_spec(owner).unwrap().invariants(),
            res.ghost_eq(self.share_with_at_spec(paddr, owner)),
            res.invariants(),
    {
        let tracked mut s = self;
        let page_model = self.get_page_ghost(paddr);
        let shared_model = page_model.share_with(owner);
        s.lemma_update_page_model_spec_with_insert_pageperm_implies_invariants(
            paddr,
            shared_model,
            init_state,
            &perm,
        );
        s.insert_pageperm(paddr, perm);
        s.update_page_model_tracked(paddr, shared_model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn transfer_at(
        tracked self,
        paddr: Paddr,
        prev_owner: PageOwner,
        new_owner: PageOwner,
    ) -> (tracked res: AbstractState)
        requires
            self.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.get_page(paddr).owners.contains(prev_owner),
            new_owner.as_usage() == self.get_page(paddr).usage,
        ensures
            self.get_page(paddr).transfer_spec(prev_owner, new_owner).is_some(),
            self.get_page(paddr).transfer_spec(prev_owner, new_owner).unwrap().invariants(),
            res == self.transfer_at_spec(paddr, prev_owner, new_owner),
            res.invariants(),
    {
        let page_model = self.get_page_ghost(paddr);
        let transferred_model = page_model.transfer(prev_owner, new_owner);
        self.lemma_get_page_implies_relate_perm(paddr);
        self.lemma_update_page_model_spec_model_relate_perm_keeps_perms_invariants(
            paddr,
            transferred_model,
        );
        assert(self.invariants()) by { admit() };
        self.update_page_model_tracked(paddr, transferred_model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_get_page_index_eq_page_to_index_spec(&self, paddr: Paddr)
        requires
            self.pages_invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            self.get_page(paddr).index == page_to_index_spec(paddr as int),
    {
        let idx = page_to_index(paddr);
        assert(self.pages.dom().contains(idx));
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_get_page_implies_relate_perm(&self, paddr: Paddr)
        requires
            self.pages_invariants(),
            self.perms_invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            self.get_page(paddr).relate_perm(self.perms[page_to_index_spec(paddr as int)]),
    {
        let idx = page_to_index(paddr);
        assert(self.pages.dom().contains(idx));
        assert(self.perms.dom().contains(idx));
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_update_page_model_spec_same_paddr_twice(
        &self,
        paddr: Paddr,
        model1: PageModel,
        model2: PageModel,
    )
        requires
            self.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            self.update_page_model_spec(paddr, model1).update_page_model_spec(paddr, model2)
                == self.update_page_model_spec(paddr, model2),
    {
        let map_direct = self.update_page_model_spec(paddr, model2).pages;
        let map_indirect = self.update_page_model_spec(paddr, model1).update_page_model_spec(
            paddr,
            model2,
        ).pages;
        assert(map_direct == map_indirect);
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_update_page_model_spec_same_model_implies_unchanged(
        &self,
        paddr: Paddr,
        model: PageModel,
    )
        requires
            self.invariants(),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.pages[page_to_index_spec(paddr as int)] == model,
        ensures
            self.update_page_model_spec(paddr, model) == self,
    {
        let map_indirect = self.update_page_model_spec(paddr, model).pages;
        let map_direct = self.pages;
        assert(map_direct == map_indirect);
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_update_page_model_spec_model_relate_perm_keeps_perms_invariants(
        tracked &self,
        paddr: Paddr,
        model: PageModel,
    )
        requires
            self.pages_invariants(),
            self.perms_invariants(),
            model.index == page_to_index_spec(paddr as int),
            model.invariants(),
            model.relate_perm(self.perms[page_to_index_spec(paddr as int)]),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
        ensures
            self.update_page_model_spec(paddr, model).perms_invariants(),
    {
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_update_page_model_spec_with_insert_pageperm_implies_invariants(
        tracked &self,
        paddr: Paddr,
        model: PageModel,
        init_state: AbstractState,
        tracked perm: &PagePerm,
    )
        requires
            init_state.invariants(),
            self.invariants(),
            self == init_state.remove_pageperm_spec(paddr),
            model.index == page_to_index_spec(paddr as int),
            model.invariants(),
            model.relate_perm(*perm),
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            perm.invariants(),
        ensures
            self.insert_pageperm_spec(paddr, *perm).update_page_model_spec(
                paddr,
                model,
            ).invariants(),
    {
        admit()
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_leak_owner_then_restore_owner_implies_unchanged(
        self,
        paddr: Paddr,
        owner: PageOwner,
        middle: AbstractState,
    )
        requires
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.invariants(),
            self.get_page(paddr).owners.contains(owner),
            middle.ghost_eq(self.leak_owner_at_spec(paddr, owner)),
        ensures
            middle.restore_owner_at_spec(paddr, owner).ghost_eq(self),
    {
        let page_model = self.get_page_ghost(paddr);
        let leaked_model = middle.get_page(paddr);
        let last_state = middle.restore_owner_at_spec(paddr, owner);
        page_model.lemma_leak_owner_then_restore_owner_implies_unchanged(owner, leaked_model);
        assert(self.pages =~= last_state.pages);
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_leak_owner_then_restore_owner_implies_transfer(
        self,
        paddr: Paddr,
        prev_owner: PageOwner,
        new_owner: PageOwner,
        middle: AbstractState,
    )
        requires
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.invariants(),
            self.get_page(paddr).owners.contains(prev_owner),
            middle.ghost_eq(self.leak_owner_at_spec(paddr, prev_owner)),
            new_owner.as_usage() == self.get_page(paddr).usage,
        ensures
            middle.restore_owner_at_spec(paddr, new_owner).ghost_eq(
                self.transfer_at_spec(paddr, prev_owner, new_owner),
            ),
    {
        let index = page_to_index_spec(paddr as int);
        let page_model = self.get_page_ghost(paddr);
        let leaked_model = middle.get_page(paddr);
        let last_state = middle.restore_owner_at_spec(paddr, new_owner);
        page_model.lemma_leak_owner_then_restore_owner_implies_transfer(
            prev_owner,
            new_owner,
            leaked_model,
        );
        assert(middle.restore_owner_at_spec(paddr, new_owner).pages =~= self.transfer_at_spec(
            paddr,
            prev_owner,
            new_owner,
        ).pages);
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_inc_then_restore_owner_implies_share_with(
        self,
        paddr: Paddr,
        owner: PageOwner,
        middle: AbstractState,
    )
        requires
            paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            self.invariants(),
            self.get_page(paddr).usage != PageUsage::Unused,
            !self.get_page(paddr).owners.is_empty(),
            middle.ghost_eq(self.inc_at_spec(paddr)),
            middle.get_page(paddr).restore_owner_spec(owner).is_some(),
        ensures
            self.share_with_at_spec(paddr, owner).ghost_eq(
                middle.restore_owner_at_spec(paddr, owner),
            ),
    {
        let page_model = self.get_page_ghost(paddr);
        let inc_model = page_model.inc();
        let last_state = middle.restore_owner_at_spec(paddr, owner);
        page_model.lemma_inc_then_restore_owner_implies_share_with(owner, inc_model);
        assert(self.share_with_at_spec(paddr, owner).pages =~= last_state.pages);
    }
}

} // verus!
