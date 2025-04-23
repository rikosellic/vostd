use vstd::prelude::*;
use vstd::set::Set;

use super::*;
use super::model::*;
use crate::common::*;

verus! {

impl PageModel {

    pub open spec fn get_vaddr_spec(&self) -> (res: int) {
        let vaddr = FRAME_METADATA_RANGE.start + self.index * META_SLOT_SIZE;
        vaddr as int
    }

    pub open spec fn get_paddr_spec(&self) -> (res: int) {
        let paddr = self.index * PAGE_SIZE;
        paddr as int
    }

    pub open spec fn from_unused_spec_failure<M: PageMeta>(paddr: Paddr,
    page: Option<Page<M>>, s1: &AbstractState, s2: &AbstractState) -> bool
    {
        page.is_none() &&
        s2.failed(&s1)
    }

    pub open spec fn from_unused_spec_success<M: PageMeta>(paddr: Paddr,
        page: Option<Page<M>>, s1: &AbstractState, s2: &AbstractState) -> bool
    {
        page.is_some() && {
            let model = s2.get_page(paddr);
            let page = page.unwrap();
            let usage = M::get_usage_spec();
            {
                page.relate_model(&model) &&
                model.invariants() &&
                model.state == usage.as_state() &&
                model.usage == usage &&
                model.ref_count == 1
            }
        }
    }

    pub open spec fn from_unused_spec<M: PageMeta>(paddr: Paddr,
        page: Option<Page<M>>, s1: &AbstractState, s2: &AbstractState) -> bool
    {
        Self::from_unused_spec_failure(paddr, page, s1, s2) || Self::from_unused_spec_success(paddr, page, s1, s2)
    }

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

    pub open spec fn new_spec(&self, usage: PageUsage, owner: PageOwner) ->
    (res: Option<PageModel,>) {
        if self.ref_count == 0 && usage != PageUsage::Unused {
            Some(
                PageModel {
                    state: usage.as_state(),
                    usage,
                    ref_count: 1,
                    owners: Set::empty().insert(owner),
                    ..*self
                },
            )
        } else {
            // reuse after free
            None
        }
    }

    pub open spec fn transfer_spec(&self, prevOwner: PageOwner, newOwner: PageOwner) -> (res: Option<
        PageModel,
    >) {
        if self.owners.contains(prevOwner) {
            Some(PageModel { owners: self.owners.remove(prevOwner).insert(newOwner), ..*self })
        } else {
            None
        }
    }

    pub open spec fn share_with_spec(&self, owner: PageOwner) -> (res: Option<PageModel>) {
        if !self.owners.is_empty() {
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

    pub open spec fn dispose_spec(&self) -> (res: PageModel) {
        PageModel {
            state: PageState::Unused,
            usage: PageUsage::Unused,
            ref_count: 0,
            owners: Set::empty(),
            ..*self
        }
    }

    pub open spec fn drop_spec(&self, owner: PageOwner) -> (res: Option<PageModel>) {
        if self.owners.contains(owner) {
            if self.owners.is_singleton() {
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
}
} // verus!
