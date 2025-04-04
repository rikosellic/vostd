#[allow(unused_imports)]
#[allow(unused)]
use builtin::*;
use builtin_macros::*;

use std::collections::HashMap;

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::cell::*;
#[allow(unused_imports)]
use vstd::hash_map::*;
#[allow(unused_imports)]
use vstd::tokens::MapToken;
#[allow(unused_imports)]
use vstd::raw_ptr::*;
use vstd::simple_pptr::*;
use vstd::simple_pptr::PointsTo;

// use crate::mm::Paddr;
// use crate::mm::Vaddr;
// use crate::mm::NR_ENTRIES;

verus! {

type Paddr = usize;
type Vaddr = usize;
pub const NR_ENTRIES: usize = 512;

pub const SIZEOF_PAGETABLEENTRY: usize = 16;
global layout PageTableEntry is size == 16, align == 8;

pub const SIZEOF_FRAME: usize = 8 + 16 * 512; // 8 bytes for pa + 8 bytes for each pte
global layout Frame is size == 8200, align == 8;

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub frame_pa: Paddr,
    pub flags: PteFlag,

    // TODO: this should not be here, just for testing {
    pub level: usize, // this should not be here, just for testing
    // pub children_addr: Paddr, // this should not be here, just for testing
    // }
}

#[derive(Clone, Copy)]
pub struct Frame {
    pub pa: Paddr,
    pub ptes: [PageTableEntry; 512],
}

tokenized_state_machine!{
PageTable {

    fields {
        #[sharding(variable)]
        pub pages: Map<Paddr, Frame>,

        #[sharding(set)]
        pub unused_addrs: Set<Paddr>,

        // TODO: clear permission management?
    }

    init!{
        initialize() {
            // TODO: 0 is a special page to indicate uninitialization
            //       maybe we need an uninitialized flag
            init pages = Map::empty().insert(0, Frame {
                ptes: [PageTableEntry {
                    frame_pa: 0,
                    flags: PteFlag,
                    level: 0,
                }; NR_ENTRIES],
                pa: 0,
            });
            init unused_addrs = Set::full().remove(0);
        }
    }

    transition! {
        // create a pte at a given address
        new_at(addr: Paddr, newFrame: Frame) {
            require addr != 0;
            require addr == newFrame.pa;
            // require newPTE.children_addr == 0;
            remove unused_addrs -= set { addr };

            update pages = pre.pages.insert(addr, newFrame);
        }
    }

    transition! {
        // set child relationship
        set_child(parent: Paddr, index: usize, child: Paddr) {
            require pre.pages.contains_key(parent);
            require pre.pages.contains_key(child);
            require pre.pages[parent].pa != pre.pages[child].pa;
            require pre.pages[parent].pa == parent;
            // require pre.pages[child].level == pre.pages[parent].level + 1;
            require pre.pages[child].pa == child;

            update pages = pre.pages.insert(parent, Frame {
                ptes: {
                    let mut ptes = pre.pages[parent].ptes;
                    // ptes[index as int].frame_pa = child; // TODO
                    ptes
                },
                pa: pre.pages[parent].pa,
            });
        }
    }

    #[inductive(set_child)]
    fn tr_set_child_invariant(pre: Self, post: Self, parent: Paddr, index: usize, child: Paddr) {
    }

    #[inductive(new_at)]
    fn tr_new_at_invariant(pre: Self, post: Self, addr: Paddr, newFrame: Frame) {
        assert(!pre.pages.contains_key(addr));
        assert(pre.unused_addrs.contains(addr));
        assert(post.pages.contains_key(addr));
        assert(post.pages[addr] == newFrame);
        assert(!post.unused_addrs.contains(addr));
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    // #[invariant]
    // pub spec fn page_wf(self) -> bool {
    //     forall |addr: Paddr| 0 <= addr <= usize::MAX ==> {
    //         if (#[trigger] self.pages.dom().contains(addr)) {
    //             let node = #[trigger] self.pages[addr];
    //             node.pa == 0 || {
    //                 node.pa == addr
    //                 &&
    //                 node.pa != node.children_addr
    //                 &&
    //                 if (node.children_addr == 0) {
    //                     true
    //                 } else if (node.children_addr != 0) {
    //                     let child = self.pages[node.children_addr];
    //                     child != node
    //                     && child.pa == node.children_addr
    //                     && child.level == node.level + 1
    //                 } else {
    //                     false
    //                 }
    //             }
    //         } else {
    //             self.unused_addrs.contains(addr)
    //         }
    //     }
    // }

    #[invariant]
    pub closed spec fn unused_addrs_are_not_in_pages(&self) -> bool {
        forall |addr: Paddr|
            #![trigger self.unused_addrs.contains(addr)]
            #![trigger self.pages.dom().contains(addr)]
            self.unused_addrs.contains(addr)
              <==> !self.pages.dom().contains(addr)
    }

    // #[invariant]
    // pub closed spec fn unused_pages_are_not_child_of_pages(&self) -> bool {
    //     forall |addr: Paddr|
    //         #![trigger self.unused_addrs.contains(addr)]
    //         self.unused_addrs.contains(addr) && addr != 0 && !self.pages.dom().contains(addr)
    //             ==> forall |parent: Paddr|
    //                 #![trigger self.pages[parent]]
    //                 #![trigger self.pages.dom().contains(parent)]
    //                 self.pages.dom().contains(parent) ==>
    //                 self.pages[parent].children_addr == 0 || self.pages[parent].children_addr != addr
    // }

}
} // tokenized_state_machine

struct_with_invariants!{
    pub struct MockPageTable {
        pub mem: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>,
        pub pages: Tracked<PageTable::pages>,
        pub instance: Tracked<PageTable::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.pages@.instance_id() == self.instance@.id()
            &&
            self.mem.len() == NR_ENTRIES
            &&
            forall |i: usize, j: usize| 0 < i < NR_ENTRIES && j == index_to_addr(i) ==>
                if (self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
                    self.pages@.value().contains_key(j)
                    &&
                    #[trigger] self.pages@.value()[j].pa == #[trigger] self.mem@[i].0.addr()
                } else {
                    true
                }
            &&
            forall |i: usize| 0 < i < NR_ENTRIES ==>
                if (#[trigger] self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
                    self.pages@.value().contains_key(self.mem@[i].0.addr())
                    &&
                    self.pages@.value()[self.mem@[i].0.addr()] == self.mem@[i].1@.value()
                } else {
                    true
                }
        }
    }
}

pub fn main() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    assert(SIZEOF_FRAME == core::mem::size_of::<Frame>());

    let tracked (Tracked(instance), Tracked(pages_token), Tracked(unused_addrs)) = PageTable::Instance::initialize();
    let tracked mut unused_addrs = unused_addrs.into_map();

    let mut fake = MockPageTable {
        mem: alloc_page_table_entries(),
        pages: Tracked(pages_token),
        instance: Tracked(instance.clone()),
    };

    assert(fake.wf());

    let (p_root, Tracked(mut pt_root)) = get_from_index(1, &fake.mem); // TODO: permission violation?

    assert(pt_root.pptr() == p_root);
    assert(pt_root.mem_contents() == MemContents::<Frame>::Uninit);
    assert(p_root.addr() + SIZEOF_FRAME == fake.mem@[2].0.addr());

    let mut f1 = Frame {
        pa: p_root.addr(),
        ptes: [PageTableEntry {
            frame_pa: 0,
            flags: PteFlag,
            level: 0,
        }; NR_ENTRIES],
    };

    assert(unused_addrs.dom().contains(p_root.addr()));
    let tracked used_addr = unused_addrs.tracked_remove(p_root.addr());

    proof{
        assert(fake.pages@.value().dom().len() == 1);
        assert(!fake.pages@.value().dom().contains(p_root.addr()));
        instance.new_at(p_root.addr(), f1, fake.pages.borrow_mut(), used_addr);
        assert(fake.pages@.value().contains_key(p_root.addr()));
    }

    assert(fake.wf());
    p_root.write(Tracked(&mut pt_root), f1);
    assert(fake.mem.len() == NR_ENTRIES);
    assert(fake.mem@.dom().contains(1));
    assert(fake.mem@.contains_key(1));

    fake.mem.remove(&1);
    assert(fake.mem.len() == NR_ENTRIES - 1);
    fake.mem.insert(1, (p_root, Tracked(pt_root)));
    assert(fake.mem.len() == NR_ENTRIES);

    assert(fake.wf());

    let (p_f2, Tracked(mut pt_f2)) = get_from_index(2, &fake.mem);

    assert(pt_f2.pptr().addr() == p_root.addr() + SIZEOF_FRAME);
    let f2 = Frame {
        pa: p_f2.addr(),
        ptes: [PageTableEntry {
            frame_pa: 0,
            flags: PteFlag,
            level: 0,
        }; NR_ENTRIES],
    };

    assert(unused_addrs.dom().contains(p_f2.addr()));
    let tracked used_addr = unused_addrs.tracked_remove(p_f2.addr());

    let tracked mut inserted_page: Tracked<PageTable::pages>;
    proof{
        assert(fake.pages@.value().dom().len() == 2);
        assert(fake.pages@.value().dom().contains(p_root.addr()));
        assert(!fake.pages@.value().dom().contains(p_f2.addr()));
        instance.new_at(p_f2.addr(), f2, fake.pages.borrow_mut(), used_addr);
    }

    p_f2.write(Tracked(&mut pt_f2), f2);
    // assert(fake.wf());

    // pte1.children_addr = pte2.pa;
    // let (p_root, Tracked(mut pt_root)) = get_from_index(1, &fake.mem); // TODO: permission violation?
    // p_root.write(Tracked(&mut pt_root), pte1);
    // proof{
    //     assert(fake.pages@.value().contains_key(p_root.addr()));
    //     assert(fake.pages@.value().contains_key(p_f2.addr()));
    //     instance.set_child(p_root.addr(), p_f2.addr(), fake.pages.borrow_mut());
    // }
    // fake.mem.remove(&1);
    // assert(fake.mem.len() == NR_ENTRIES - 1);
    // fake.mem.insert(1, (p_root, Tracked(pt_root)));

    // assert(fake.wf());

    print_mem(fake.mem);

}

#[verifier::external_body]
fn alloc_page_table_entries() -> (res: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>)
    ensures
        res@.dom().len() == NR_ENTRIES,
        res@.len() == NR_ENTRIES,
        res.len() == NR_ENTRIES,
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            res@.dom().contains(i)
        },
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            res@.contains_key(i)
        },
        forall |i:usize| 0 < i < NR_ENTRIES ==> {
            (#[trigger] res@[i]).1@.pptr() == res@[i].0
        },
        forall |i:usize| 0 < i < NR_ENTRIES ==> {
            #[trigger] res@[i].1@.mem_contents() == MemContents::<Frame>::Uninit
        },
        forall |i:usize, j:usize| 0 < i < j < NR_ENTRIES && i == j - 1 ==> {
            && (#[trigger] res@[i]).0.addr() + SIZEOF_FRAME == (#[trigger] res@[j]).0.addr() // pointers are adjacent
        },
        res@[0].0.addr() == 0,
        res@[1].0.addr() == PHYSICAL_BASE_ADDRESS_SPEC(), // points to the hardware page table
        res@.dom().finite(),
{
    let mut map = HashMap::<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>::new();
    map.insert(0, (PPtr::from_addr(0), Tracked::assume_new()));
    let p = PHYSICAL_BASE_ADDRESS();
    for i in 1..NR_ENTRIES {
        map.insert(
            i,
            (
                PPtr::from_addr(p + i * SIZEOF_FRAME),
                Tracked::assume_new()
            )
        );
    }
    map
}

#[verifier::external_body]
fn get_from_index(index: usize, map: &HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>) -> (res: (PPtr<Frame>, Tracked<PointsTo<Frame>>))
    requires
        0 <= index < NR_ENTRIES,
        map@.dom().contains(index),
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            map@.dom().contains(i)
        },
        forall |i:usize| 0 < i < NR_ENTRIES ==> {
            (#[trigger] map@[i]).1@.pptr() == map@[i].0
        }
    ensures
        res.0.addr() != 0,
        res.1@.pptr() == res.0,
        // NOTE: this is not true! && res.0.addr() == map@[index]@.0.addr()
        res.0 == map@[index].0,
        res.1 == map@[index].1
{
    let (p, Tracked(pt)) = map.get(&index).unwrap();
    (*p, Tracked::assume_new())
}

pub open spec fn index_to_addr(index: usize) -> usize {
    (PHYSICAL_BASE_ADDRESS_SPEC() + (index - 1) * SIZEOF_PAGETABLEENTRY) as usize
}

// TODO: can we eliminate division
pub open spec fn addr_to_index(addr: usize) -> usize {
    ((addr - PHYSICAL_BASE_ADDRESS_SPEC()) / SIZEOF_PAGETABLEENTRY as int + 1) as usize
}

pub open spec fn PHYSICAL_BASE_ADDRESS_SPEC() -> usize {
    0x1000
}

#[allow(unused_imports)]
use std::alloc::{alloc, dealloc, Layout};

#[verifier::external_body]
pub fn PHYSICAL_BASE_ADDRESS() -> (res: usize)
ensures
    res == PHYSICAL_BASE_ADDRESS_SPEC()
{
    unsafe{
        let layout = Layout::new::<[PageTableEntry; 4096]>();
        let mut ptr = alloc(layout);
        ptr as *mut u8 as usize
    }
}

#[verifier::external_body]
fn print_mem(mem: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>) {
    // print 1
    let (p, Tracked(mut pt)) = mem.get(&1).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("PTE1: pa: {}", frame.pa);

    // print 2
    let (p, Tracked(mut pt)) = mem.get(&2).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("PTE2: pa: {}", frame.pa);
}

} // verus!
