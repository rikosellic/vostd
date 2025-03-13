use state_machines_macros::*;
use vstd::prelude::*;

use crate::Vaddr;
use crate::Paddr;

verus! {

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub pa: Paddr,
    pub flags: PteFlag,
}

tokenized_state_machine!{
PageTable {

    fields {
        #[sharding(map)]
        pub pages: Map<Paddr, Option<PageTableEntry>>,
    }

    init!{
        initialize() {
            init pages = Map::new(|p: Paddr| true, |p: Paddr| None);
        }
    }

    transition! {
        // create a child at the first index of the target node
        new_at(addr: Paddr, node: PageTableEntry) {
            remove pages -= [ addr => let old_node ];
            add pages += [addr => Some(node)];
        }
    }

    #[inductive(new_at)]
    fn tr_new_at_zero_invariant(pre: Self, post: Self, addr: Paddr, node: PageTableEntry) {
    }

}
} // tokenized_state_machine

struct_with_invariants!{
    pub struct FakePageTable {
        pub pages: [Option<PageTableEntry>; 512], // lock? PCell?

        pub ghost_pages: Tracked<PageTable::pages>,
        pub page_table_model: Tracked<PageTable::Instance>
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            forall |i:int| 0 <= i < 512 ==> {
                // TODO
                // self.pages[i].is_some() == self.ghost_pages[i]@.is_some()
                true
            }
        }
    }
}

fn main() {
    let tracked (Tracked(instance), Tracked(pages)) = PageTable::Instance::initialize();

    let INIT: Option<PageTableEntry> = None;

    let fake = FakePageTable {
        pages: [INIT; 512],
        ghost_pages: pages,
        page_table_model: Tracked(instance.clone()),
    };

    fake.pages[0] = Some(PageTableEntry {
        pa: &fake.pages[0], // something like the physical address of the page table entry
        flags: PteFlag,
    });
}

} // verus!
