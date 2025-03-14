use state_machines_macros::*;
use vstd::prelude::*;
use vstd::cell::*;
use vstd::hash_map::*;

use crate::Vaddr;
use crate::Paddr;

verus! {

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub pa: Paddr,
    pub flags: PteFlag,

    pub level: nat, // this should not be here, just for testing
    pub ghost children: Paddr, // this should not be here, just for testing
}

tokenized_state_machine!{
PageTable {

    fields {
        #[sharding(map)]
        pub pages: Map<Paddr, PageTableEntry>,
    }

    init!{
        initialize() {
            init pages = Map::new(|p: Paddr| 0 <= p <= usize::MAX, |p: Paddr| PageTableEntry {
                pa: p,
                flags: PteFlag,

                level: 0,
                children: 0,
            });
        }
    }

    transition! {
        // create a child at the first index of the target node
        new_at(addr: Paddr, node: PageTableEntry) {
            remove pages -= [ addr => let old_node ];
            add pages += [addr => node];
        }
    }

    #[inductive(new_at)]
    fn tr_new_at_invariant(pre: Self, post: Self, addr: Paddr, node: PageTableEntry) {
            // assert(!pre.pages.contains_key(addr)); // failed, why?
            assert(post.pages.contains_key(addr));
            assert(post.pages[addr] == node);
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[invariant]
    pub spec fn page_wf(self) -> bool {
        true
    }

    pub open spec fn pages(&self) -> Map<Paddr, PageTableEntry> {
        self.pages
    }

    pub open spec fn len(&self) -> nat {
        self.pages.len()
    }

}
} // tokenized_state_machine

struct_with_invariants!{
    pub struct FakePageTable {
        pub mem: *mut u8, // lock? PCell?
        pub instance: Tracked<PageTable::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            // for all pages
            // forall |i:int| 0 <= i < self.instance@.pages().len() ==> { // no len method?
            //     self.mem.addr() <= #[trigger] self.instance@.pages()[i as usize].pa
            // }
            true
        }
    }
}

#[verifier::external_body]
fn alloc_mut_u8() -> *mut u8 {
    unsafe { std::alloc::alloc(std::alloc::Layout::new::<[u8;10000]>()) }
}

fn main() {
    let tracked (Tracked(instance), Tracked(pages)) = PageTable::Instance::initialize();

    let mut fake = FakePageTable {
        mem: alloc_mut_u8(),
        // ghost_pages: pages,
        instance: Tracked(instance.clone()),
    };

    // fake.mem[0] = Some(PageTableEntry {
    //     pa: &fake.pages[0], // something like the physical address of the page table entry
    //     flags: PteFlag,
    // });
}

} // verus!
