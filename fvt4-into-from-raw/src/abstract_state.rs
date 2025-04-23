use vstd::prelude::*;

use super::page::model::*;
use super::page::meta::model::*;
use super::common::*;

verus! {

pub tracked struct AbstractState {
    pub ghost meta_slots: Map<int, MetaSlotModel>,
    pub ghost pages: Map<int, PageModel>,
    pub ghost max_pages: int,
    pub ghost errors: Seq<&'static str>,
    pub ghost context_id: int,
    pub ghost thread_id: int,
}

} // verus!
verus! {

impl AbstractState {
    pub open spec fn max_page_invariants(&self) -> bool {
        0 < self.max_pages && self.max_pages <= MAX_NR_PAGES
    }

    pub open spec fn pages_invariants(&self) -> bool {
        &&& forall|i: int|
            {
                0 <= i && i < MAX_NR_PAGES ==> {
                    #[trigger] self.pages.dom().contains(i) && self.pages[i].index == i
                        && self.pages[i].invariants()
                }
            }
    }

    pub open spec fn meta_slots_invariants(&self) -> bool {
        &&& forall|i: int|
            {
                0 <= i && i < MAX_NR_PAGES ==> {
                    #[trigger] self.meta_slots.dom().contains(i) && self.meta_slots[i].address@ == i
                        * PAGE_SIZE && self.meta_slots[i].invariants()
                }
            }
    }

    pub open spec fn invariants(&self) -> bool {
        self.max_page_invariants() && self.pages_invariants() && self.meta_slots_invariants()
    }

    pub open spec fn get_page(&self, paddr: u64) -> (res: &PageModel) {
        &self.pages[paddr as int / PAGE_SIZE as int]
    }

    pub open spec fn get_meta_slot(&self, paddr: u64) -> (res: &MetaSlotModel) {
        &self.meta_slots[paddr as int / PAGE_SIZE as int]
    }

    pub proof fn get_page_relate_to_paddr(&self, paddr: Paddr)
        requires
            self.invariants(),
            paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
        ensures
            self.get_page(paddr).relate_paddr(paddr),
    {
        let page = self.get_page(paddr);
        let idx = paddr as int / PAGE_SIZE as int;
        assert(page == &self.pages[idx]);
        assert(self.pages.dom().contains(idx));
        assert(self.pages[idx].index == idx);
        assert(page.index == idx);
        assert(page.index == paddr as int / PAGE_SIZE as int);
        assert(page.index * PAGE_SIZE as int == paddr as int);
        assert(page.relate_paddr(paddr));
    }

    pub proof fn get_meta_slot_relate_to_paddr(&self, paddr: Paddr)
        requires
            self.invariants(),
            paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
        ensures
            self.get_meta_slot(paddr).address@ == paddr,
    {
        let slot = self.get_meta_slot(paddr);
        let idx = paddr as int / PAGE_SIZE as int;
        assert(slot == &self.meta_slots[idx]);
        assert(self.meta_slots.dom().contains(idx));
        assert(self.meta_slots[idx].address@ == idx * PAGE_SIZE);
        assert(slot.address@ == idx * PAGE_SIZE);
        assert(slot.address@ == paddr);
    }

    pub open spec fn panic_spec(&self, msg: &str) -> AbstractState {
        AbstractState { errors: self.errors.push(msg), ..*self }
    }

    pub open spec fn failed(&self, initial: &AbstractState) -> bool {
        self.errors.len() > initial.errors.len()
    }
}

pub fn panic(Tracked(s): Tracked<AbstractState>, msg: &str) -> (res: Tracked<AbstractState>)
    ensures
        res@ == s.panic_spec(msg),
{
    Tracked(AbstractState { errors: s.errors.push(msg), ..s })
}

} // verus!
