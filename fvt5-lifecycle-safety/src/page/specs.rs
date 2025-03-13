extern crate vstd_extra;
use vstd::prelude::*;
use vstd::multiset::Multiset;
use vstd::simple_pptr::{PPtr, PointsTo};
use super::model::*;
use aster_common::prelude::*;

verus! {

impl PageModel {

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_vaddr_spec(&self) -> (res: int) {
        let vaddr = FRAME_METADATA_RANGE().start + self.index * META_SLOT_SIZE();
        vaddr as int
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_paddr_spec(&self) -> (res: int) {
        let paddr = self.index * PAGE_SIZE_SPEC();
        paddr as int
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_unused_spec_failure<M: PageMeta>(paddr: Paddr,
    page: Option<Page<M>>, owner:PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        page.is_none() &&
        s2.failed(s1)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_unused_spec_success<M: PageMeta>(paddr: Paddr,
        page: Option<Page<M>>, owner:PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        page.is_some() && {
            let model = s2.get_page(paddr);
            let page = page.unwrap();
            let usage = M::USAGE_spec();
            {
                &&& page.relate_model(model)
                &&& model.invariants()
                &&& model.state == usage.as_state()
                &&& model.usage == usage
                &&& model.ref_count == 1
                &&& model.owners =~= Multiset::singleton(owner)
                &&& s2.ghost_eq(s1.update_page_model_spec(paddr,model))
            }

        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_unused_spec<M: PageMeta>(paddr: Paddr,
        page: Option<Page<M>>, owner: PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        Self::from_unused_spec_failure(paddr, page, owner, s1, s2) || Self::from_unused_spec_success(paddr, page, owner, s1, s2)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn permission(&self, perm: PageUsePermission) -> bool {
        if perm == PageUsePermission::NoPerm {
            true
        } else {
            match self.usage {
                PageUsage::Frame => {
                    perm == PageUsePermission::ReadWrite
                },
                PageUsage::PageTable => {
                    ||| perm == PageUsePermission::PageTableEntry
                    ||| perm == PageUsePermission::RawPointer
                },
                PageUsage::Meta => {
                    perm == PageUsePermission::RawPointer
                },
                _ => false,
            }
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn transfer_spec(&self, prev_owner: PageOwner, new_owner: PageOwner) -> (res: Option<
        PageModel,
    >) {
        if self.owners.contains(prev_owner) && new_owner.as_usage() == self.usage {
            Some(PageModel { owners: self.owners.remove(prev_owner).insert(new_owner), ..*self })
        } else {
            None
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn share_with_spec(&self, owner: PageOwner) -> (res: Option<PageModel>) {
        if !self.owners.is_empty() && owner.as_usage() == self.usage {
            Some(
                PageModel {
                    ref_count: self.ref_count + 1,
                    owners: self.owners.insert(owner),
                    ..*self
                },
            )
        } else {
            // cannot share unused page
            None
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn dispose_spec(&self) -> (res: PageModel) {
        PageModel {
            state: PageState::Unused,
            usage: PageUsage::Unused,
            ref_count: 0,
            owners: Multiset::empty(),
            ..*self
        }
    }

    #[rustc_allow_incoherent_impl]
    /// Drop the page model with the given owner, dispose_spec is called if the ref_count is 1.
    pub open spec fn drop_spec(&self, owner: PageOwner) -> (res: Option<PageModel>) {
        if self.owners.contains(owner) {
            if self.ref_count == 1 {
                Some(self.dispose_spec())
            } else {
                Some(PageModel {
                        ref_count: self.ref_count - 1,
                        owners: self.owners.remove(owner),
                        ..*self
                    })
                }
        } else {
            // double free
            None
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn leak_owner_spec(&self,owner: PageOwner) -> (res: Option<PageModel>) {
        if self.owners.contains(owner) {
            Some(PageModel {
                owners: self.owners.remove(owner),
                ..*self
            })
        } else {
            None
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn restore_owner_spec(&self, owner: PageOwner) -> (res: Option<PageModel>) {
        if self.isleaked() && owner.as_usage() == self.usage {
            Some(PageModel {
                owners: self.owners.insert(owner),
                ..*self
            })
        } else {
            None
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inc_spec(&self) -> (res: Option<PageModel>) {
        if self.usage != PageUsage::Unused {
            Some(PageModel {
                ref_count: self.ref_count + 1,
                ..*self
            })
        } else {
            None
        }
    }

}
} // verus!

verus! {

impl PageModel {

    #[rustc_allow_incoherent_impl]
    pub open spec fn into_raw_spec<M: PageMeta>(
        page: Page<M>, owner:PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        let paddr = page.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& page.relate_model(model1)
            &&& model2.invariants()
            &&& s2 == s1.leak_owner_at_spec(paddr,owner)
            //&&& model1.leak_owner_spec(owner) == Some(model2)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn dynpage_into_raw_spec(
        page: DynPage, owner:PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        let paddr = page.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& page.relate_model(model1)
            &&& model2.invariants()
            &&& s2 == s1.leak_owner_at_spec(paddr,owner)
            //&&& model1.leak_owner_spec(owner) == Some(model2)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_raw_spec<M:PageMeta>(
        page: Page<M>, owner: PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        let paddr = page.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& model1.isleaked()
            &&& page.relate_model(model2)
            &&& model2.invariants()
            && s2 == s1.restore_owner_at_spec(paddr,owner)
            //&&& model1.restore_owner_spec(owner) == Some(model2)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn dynpage_from_raw_spec(
        page: DynPage, owner: PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        let paddr = page.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& model1.isleaked()
            &&& page.relate_model(model2)
            &&& model2.invariants()
            && s2 == s1.restore_owner_at_spec(paddr,owner)
            //&&& model1.restore_owner_spec(owner) == Some(model2)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn clone_spec<M:PageMeta>(
        page: Page<M>, owner: PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        let paddr = page.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& page.relate_model(model1)
            &&& model2.invariants()
            &&& s2.ghost_eq(s1.share_with_at_spec(paddr,owner))
            //&&& model1.share_with_spec(owner) == Some(model2)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn dynpage_clone_spec(
        page: DynPage, owner: PageOwner, s1: AbstractState, s2: AbstractState) -> bool
    {
        let paddr = page.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& page.relate_model(model1)
            &&& model2.invariants()
            &&& s2.ghost_eq(s1.share_with_at_spec(paddr,owner))
            //&&& model1.share_with_spec(owner) == Some(model2)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inc_page_ref_count_spec(
        paddr: Paddr, s1: AbstractState, s2: AbstractState) -> bool
    {
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            //&&& model1.inc_spec() == Some(model2)
            &&& model2.invariants()
            &&& model2.isleaked()
            &&& s2.ghost_eq(s1.inc_at_spec(paddr))
        }
    }

}

}
