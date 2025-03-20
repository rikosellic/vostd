#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use std::intrinsics::size_of;

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::cell::*;
use vstd::hash_map::*;
use vstd::tokens::MapToken;
use vstd::raw_ptr::*;
use vstd::simple_pptr::*;
use vstd::simple_pptr::PointsTo;

use crate::mm::Vaddr;
use crate::mm::Paddr;
use crate::mm::NR_ENTRIES;

verus! {

pub const SIZEOF_PAGETABLEENTRY: usize = 24;
global layout PageTableEntry is size == 24, align == 8; // TODO: is this true?

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub pa: Paddr,
    pub flags: PteFlag,

    pub level: usize, // this should not be here, just for testing
    pub children_addr: Paddr, // this should not be here, just for testing
}

tokenized_state_machine!{
PageTable {

    fields {
        #[sharding(map)]
        pub pages: Map<Paddr, PageTableEntry>,

        #[sharding(set)]
        pub unused_addrs: Set<Paddr>,
    }

    init!{
        initialize() {
            // TODO: 0 is a special page to indicate uninitialization
            init pages = Map::empty().insert(0, PageTableEntry {
                pa: 0,
                flags: PteFlag,
                level: 0,
                children_addr: 0,
            });
            init unused_addrs = Set::full().remove(0);
        }
    }

    transition! {
        // create a child at the first index of the target node
        new_at(addr: Paddr, newPTE: PageTableEntry) {
            require addr != 0;
            require addr == newPTE.pa;
            require newPTE.children_addr == 0;
            remove unused_addrs -= set { addr };
            add pages += [addr => newPTE];
        }
    }

    #[inductive(new_at)]
    fn tr_new_at_invariant(pre: Self, post: Self, addr: Paddr, newPTE: PageTableEntry) {
        assert(!pre.pages.contains_key(addr));
        assert(pre.unused_addrs.contains(addr));
        assert(post.pages.contains_key(addr));
        assert(post.pages[addr] == newPTE);
        assert(!post.unused_addrs.contains(addr));
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[invariant]
    pub spec fn page_wf(self) -> bool {
        forall |addr: Paddr| 0 <= addr <= usize::MAX ==> {
            if (#[trigger] self.pages.dom().contains(addr)) {
                let node = #[trigger] self.pages[addr];
                node.pa == 0 || {
                    node.pa == addr
                    &&
                    node.pa != node.children_addr
                    &&
                    if (node.children_addr == 0) {
                        true
                    } else if (node.children_addr != 0) {
                        let child = self.pages[node.children_addr];
                        child != node
                        && child.pa == node.children_addr
                        && child.level == node.level + 1
                    } else {
                        false
                    }
                }
            } else {
                self.unused_addrs.contains(addr)
            }
        }
    }

    #[invariant]
    pub closed spec fn unused_addrs_are_not_in_pages(&self) -> bool {
        forall |addr: Paddr|
            #![trigger self.unused_addrs.contains(addr)]
            #![trigger self.pages.dom().contains(addr)]
            self.unused_addrs.contains(addr)
              <==> !self.pages.dom().contains(addr)
    }

    #[invariant]
    pub closed spec fn unused_pages_are_not_child_of_pages(&self) -> bool {
        forall |addr: Paddr|
            #![trigger self.unused_addrs.contains(addr)]
            self.unused_addrs.contains(addr) && addr != 0 && !self.pages.dom().contains(addr)
                ==> forall |parent: Paddr|
                    #![trigger self.pages[parent]]
                    #![trigger self.pages.dom().contains(parent)]
                    self.pages.dom().contains(parent) ==>
                    self.pages[parent].children_addr == 0 || self.pages[parent].children_addr != addr
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
    pub struct MockPageTable {
        pub mem: HashMapWithView<usize, Tracked<(PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>)>>,
        pub pages: Tracked<MapToken<usize, PageTableEntry, PageTable::pages>>,
        pub instance: Tracked<PageTable::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.pages@.instance_id() == self.instance@.id()
            &&
            self.mem.len() == NR_ENTRIES
            &&
            forall |i: usize| 0 <= i < NR_ENTRIES ==>
                if (self.pages@.dom().contains(i)) {
                    #[trigger] self.pages@[i].pa == self.mem@[i]@.0.addr()
                } else {
                    true
                }
        }
    }
}

fn main() {
    assert(SIZEOF_PAGETABLEENTRY == core::mem::size_of::<PageTableEntry>());

    let tracked (Tracked(instance), Tracked(pages_token), Tracked(unused_addrs)) = PageTable::Instance::initialize();
    let tracked mut unused_addrs = unused_addrs.into_map();

    let fake = MockPageTable {
        mem: alloc_page_table_entries(),
        pages: Tracked(pages_token),
        instance: Tracked(instance.clone()),
    };

    assert(fake.wf());

    assert(
            forall |i:usize| 0 < i < NR_ENTRIES ==> {
                fake.mem@.dom().contains(i)
                && (#[trigger] fake.mem@[i])@.1@.pptr() == fake.mem@[i]@.0
                && (#[trigger] fake.mem@[i])@.1@.mem_contents() == MemContents::<PageTableEntry>::Uninit
            }
            &&
            forall |i:usize, j: usize| 0 < i < j < NR_ENTRIES && i == j - 1 ==> {
                fake.mem@.dom().contains(i)
                && fake.mem@.dom().contains(j)
                && (#[trigger] fake.mem@[i])@.0.addr() + SIZEOF_PAGETABLEENTRY == (#[trigger] fake.mem@[j])@.0.addr() // pointers are adjacent
            }
            && fake.mem@[0]@.0.addr() == 0 // points to the hardware page table
            && fake.mem@.dom().contains(0)
            );
    assert(fake.mem@.dom().contains(0 as usize));
    assert(fake.mem@.dom().contains(0));

    let (p_root, Tracked(mut pt_root)) = get_from_index(1, &fake.mem);
    assert(pt_root.pptr() == p_root);
    // assert(pt_root.mem_contents() == MemContents::<PageTableEntry>::Uninit);
    assert(p_root.addr() + SIZEOF_PAGETABLEENTRY == fake.mem@[2]@.0.addr());

    let pte1 = PageTableEntry {
        pa: p_root.addr(),
        flags: PteFlag,
        level: 0,
        children_addr: 0,
        // children_index: 0,
    };

    assert(unused_addrs.dom().contains(p_root.addr()));
    let tracked used_addr = unused_addrs.tracked_remove(p_root.addr());

    proof{
        assert(pages_token.dom().len() == 1);
        assert(fake.pages@.dom().len() == 1);
        assert(!fake.pages@.dom().contains(p_root.addr()));
        let tracked inserted_page = instance.new_at(p_root.addr(), pte1, used_addr);
        // fake.pages@.into_map().insert(p_root.addr(), inserted_page_token);
        assert(fake.wf());
        // fake.pages@[0] = inserted_page_token;
    }

    p_root.write(Tracked(&mut pt_root), pte1);

    // let (p_pte2, Tracked(mut pt_pte2)) = get_from_index(1, &fake.mem);
    // let pte2 = PageTableEntry {
    //     pa: p_root.addr() + SIZEOF_PAGETABLEENTRY,
    //     flags: PteFlag,
    //     level: 1,
    //     children: 0,
    //     children_index: 0,
    // };

    // assert(pt_pte2.addr() != p_root.addr());
    // assert(unused_addrs.dom().contains(p_pte2.addr()));
    // let tracked used_addr = unused_addrs.tracked_remove(p_pte2.addr());

    // proof{
    //     assert(pages_token.dom().len() == 0);
    //     assert(fake.pages@.dom().len() == 0);
    //     assert(fake.pages@.dom().contains(p_root.addr()));
    //     assert(!fake.pages@.dom().contains(p_root.addr()));
    //     // TODO: this should not be passed?!?!
    //     instance.new_at(p_root.addr(), pte2, used_addr);
    //     assert(fake.wf());
    //     assert(fake.pages@.dom().contains(pt_pte2.addr()));
    // }

    // p_pte2.write(Tracked(&mut pt_pte2), pte2);

    // proof{
    //     // assert(forall|i:usize| 0 <= i < 1000 ==> {
    //     //     let (p, Tracked(mut pt)) = get_from_index(i, &mem);
    //     //     if (p.borrow(Tracked(&mut pt)).children != 0)
    //     //     {
    //     //         let (p2, Tracked(mut pt2)) = get_from_index(p.borrow(Tracked(&mut pt)).children_index, &mem);
    //     //         p.borrow(Tracked(&mut pt)).children == p2.borrow(Tracked(&mut pt2)).pa
    //     //     } else {
    //     //         true
    //     //     }}
    //     // );
    // }

}

#[verifier::external_body]
fn alloc_page_table_entries() -> (res: HashMapWithView<usize, Tracked<(PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>)>>)
    ensures
        res@.dom().len() == NR_ENTRIES,
        res@.len() == NR_ENTRIES,
        res.len() == NR_ENTRIES,
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            res@.dom().contains(i)
        },
        forall |i:usize| 0 < i < NR_ENTRIES ==> {
            (#[trigger] res@[i])@.1@.pptr() == res@[i]@.0
        },
        forall |i:usize| 0 < i < NR_ENTRIES ==> {
            #[trigger] res@[i]@.1@.mem_contents() == MemContents::<PageTableEntry>::Uninit
        },
        forall |i:usize, j:usize| 0 < i < j < NR_ENTRIES && i == j - 1 ==> {
            && (#[trigger] res@[i])@.0.addr() + SIZEOF_PAGETABLEENTRY == (#[trigger] res@[j])@.0.addr() // pointers are adjacent
        },
        res@[0]@.0.addr() == 0, // points to the hardware page table
        res@[1]@.0.addr() == 0x100, // points to the hardware page table
{
    unimplemented!()
}

#[verifier::external_body]
fn get_from_index(index: usize, map: &HashMapWithView<usize, Tracked<(PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>)>>) -> (res: (PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>))
    requires
        0 <= index < NR_ENTRIES,
        map@.dom().contains(index),
        map@.len() == NR_ENTRIES,
        map@.dom().len() == NR_ENTRIES,
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            map@.dom().contains(i)
        },
        forall |i:usize| 0 < i < NR_ENTRIES ==> {
            (#[trigger] map@[i]@).1@.pptr() == map@[i]@.0
        }
            // && map@[i]@.1@.mem_contents() == MemContents::<PageTableEntry>::Uninit
            // && map@[i]@.0.addr() + SIZEOF_PAGETABLEENTRY == map@[((i + 1) as usize)]@.0.addr() // pointers are adjacent
            // && map@[i]@.0.addr() == 0x1000 // points to the hardware page table
    ensures
        res.0.addr() != 0,
        res.1@.pptr() == res.0,
        // NOTE: this is not true! && res.0.addr() == map@[index]@.0.addr()
        res.0 == map@[index]@.0,
        res.1 == map@[index]@.1
{
    unimplemented!()
}
} // verus!
