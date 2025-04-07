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

pub const SIZEOF_FRAME: usize = 16 * 512; // 8 bytes for pa + 8 bytes for each pte
global layout Frame is size == 8192, align == 8;

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct Frame {
    // pub pa: Paddr,
    pub ptes: [PageTableEntry; 512],
    // pub has_ptes: bool,
}
#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub frame_pa: Paddr,
    pub flags: PteFlag,
    pub level: usize,
}

pub ghost struct PageTableEntryView {
    pub frame_pa: int,
    pub flags: PteFlag,
    pub level: usize,
}

pub ghost struct FrameView {
    pub pa: int,
    // pub ptes: [PageTableEntry; 512],
    pub pte_addrs: Seq<int>,
}
}

tokenized_state_machine! {
SimplePageTable {

    fields {
        #[sharding(variable)]
        pub frames: Map<int, FrameView>,

        #[sharding(set)]
        pub unused_addrs: Set<int>,

        #[sharding(variable)]
        pub ptes: Map<int, PageTableEntryView>,

        #[sharding(set)]
        pub unused_pte_addrs: Set<int>,
    }

    init!{
        initialize() {
            init frames = Map::empty();
            init unused_addrs = Set::full();

            init ptes = Map::empty();
            init unused_pte_addrs = Set::full();
        }
    }

    transition! {
        // create a pte at a given address
        new_at(addr: int, newFrame: FrameView) {
            require addr != 0;
            require addr == newFrame.pa;
            // require forall |i: int| 0 <= i < NR_ENTRIES ==> #[trigger] newFrame.ptes[i].frame_pa == 0;
            require newFrame.pte_addrs.len() == 0;
            require forall |i: int| 0 <= i < NR_ENTRIES ==>
                !#[trigger]pre.ptes.dom().contains(newFrame.pa + i * SIZEOF_PAGETABLEENTRY);
            remove unused_addrs -= set { addr };

            update frames = pre.frames.insert(addr, newFrame);
        }
    }

    transition! {
        // set child relationship
        set_child(parent: int, index: usize, child: int, level: usize) {
            require parent != child;
            require pre.frames.contains_key(parent);
            require pre.frames.contains_key(child);
            require pre.frames[parent].pa != pre.frames[child].pa;
            require pre.frames[parent].pa == parent;
            require pre.frames[child].pte_addrs.len() == 0;
            require forall |i: int| 0 <= i < Paddr::MAX ==>
                #[trigger] pre.ptes.contains_key(i) && #[trigger] pre.ptes[i].frame_pa == parent ==> pre.ptes[i].level == level + 1;
            require forall |i: int| 0 <= i < Paddr::MAX ==>
                #[trigger] pre.ptes.contains_key(i) ==> #[trigger] pre.ptes[i].frame_pa != child;

            require pre.frames[child].pa == child;
            let pte_addr = parent + index * SIZEOF_PAGETABLEENTRY;
            require !pre.frames[parent].pte_addrs.contains(pte_addr);
            require !pre.ptes.dom().contains(pte_addr);

            update frames = pre.frames.insert(parent, FrameView {
                pa: pre.frames[parent].pa,
                pte_addrs: pre.frames[parent].pte_addrs.push(pte_addr),
            });

            remove unused_pte_addrs -= set { pte_addr };

            update ptes = pre.ptes.insert(
                pte_addr,
                PageTableEntryView {
                    frame_pa: child,
                    flags: PteFlag,
                    level: level,
                }
            );
        }
    }

    #[inductive(set_child)]
    pub fn tr_set_child_invariant(pre: Self, post: Self, parent: int, index: usize, child: int, level: usize) {
        assert(pre.frames.contains_key(parent));
        assert(pre.frames.contains_key(child));
        assert(pre.frames[parent].pa != pre.frames[child].pa);
        assert(pre.frames[parent].pa == parent);
        assert(pre.frames[child].pa == child);
        assert(pre.unused_pte_addrs.contains(parent + index * SIZEOF_PAGETABLEENTRY));

        assert(post.ptes.dom().contains(parent + index * SIZEOF_PAGETABLEENTRY));
    }

    #[inductive(new_at)]
    pub fn tr_new_at_invariant(pre: Self, post: Self, addr: int, newFrame: FrameView) {
        assert(!pre.frames.contains_key(addr));
        assert(pre.unused_addrs.contains(addr));
        assert(post.frames.contains_key(addr));
        assert(post.frames[addr] == newFrame);
        assert(!post.unused_addrs.contains(addr));
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self) { }

    #[invariant]
    pub spec fn page_wf(self) -> bool {
        forall |addr: int| 0 <= addr <= usize::MAX ==> {
            if (#[trigger] self.frames.dom().contains(addr)) {
                let node = #[trigger] self.frames[addr];
                node.pa == addr
                &&
                forall |i: int|
                #![trigger node.pte_addrs[i]]
                0 <= i < node.pte_addrs.len() ==>
                {
                    let pte_addr = node.pte_addrs[i];
                    if (self.ptes.dom().contains(pte_addr)) { // pte_addr is a valid pte address

                        let pte = self.ptes[pte_addr];
                        self.frames.dom().contains(pte.frame_pa)
                        &&
                        self.frames[pte.frame_pa].pa == pte.frame_pa

                        // // TODO: child level relation
                        // &&
                        // if (self.frames.dom().contains(pte.frame_pa)) {
                        //     let child = self.frames[pte.frame_pa];
                        //     forall |j: int|
                        //     #![trigger child.pte_addrs[j]]
                        //     0 <= j < child.pte_addrs.len() ==>
                        //     {
                        //         let child_pte_addr = child.pte_addrs[j];
                        //         if (self.ptes.dom().contains(child_pte_addr)) {
                        //             self.ptes[child_pte_addr].level == pte.level + 1
                        //         } else {
                        //             false
                        //         }
                        //     }
                        // } else {
                        //     true
                        // }

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
    pub closed spec fn unused_addrs_are_not_in_frames(&self) -> bool {
        forall |addr: int|
            #![trigger self.unused_addrs.contains(addr)]
            #![trigger self.frames.dom().contains(addr)]
            self.unused_addrs.contains(addr)
              <==> !self.frames.dom().contains(addr)
        &&
        forall |addr: int|
            #![trigger self.ptes.dom().contains(addr)]
            #![trigger self.unused_pte_addrs.contains(addr)]
            self.unused_pte_addrs.contains(addr)
              <==> !self.ptes.dom().contains(addr)
    }

    // TODO: is this invariant correct?
    // #[invariant]
    // pub closed spec fn unused_frames_are_not_child_of_frames(&self) -> bool {
    //     forall |addr: int|
    //         #![trigger self.unused_addrs.contains(addr)]
    //         self.unused_addrs.contains(addr)
    //             ==> forall |parent: int|
    //                 #![trigger self.frames[parent]]
    //                 #![trigger self.frames.dom().contains(parent)]
    //                 self.frames.dom().contains(parent) ==>
    //                 self.frames[parent].pa != addr
    //                 &&
    //                 forall |i: int|
    //                 #![trigger self.frames[parent].pte_addrs[i]]
    //                 0 <= i < self.frames[parent].pte_addrs.len() ==> {
    //                     let pte_addr = self.frames[parent].pte_addrs[i];
    //                     pte_addr != addr
    //                 }
    // }

}
} // tokenized_state_machine

struct_with_invariants! {
    pub struct MockPageTable {
        pub mem: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>,
        pub frames: Tracked<SimplePageTable::frames>,
        pub instance: Tracked<SimplePageTable::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.frames@.instance_id() == self.instance@.id()
            &&
            self.mem.len() == NR_ENTRIES
            &&
            forall |i: usize, j: usize| 0 < i < NR_ENTRIES && j == index_to_addr(i) ==>
                if (self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
                    self.frames@.value().contains_key(j as int)
                    &&
                    #[trigger] self.frames@.value()[j as int].pa == #[trigger] self.mem@[i].0.addr()
                } else {
                    true
                }
            // &&
            // forall |i: usize| 0 < i < NR_ENTRIES ==>
            //     if (#[trigger] self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
            //         self.frames@.value().contains_key(self.mem@[i].0.addr())
            //         &&
            //         self.frames@.value()[self.mem@[i].0.addr()] == self.mem@[i].1@.value()
            //     } else {
            //         true
            //     }
        }
    }
}

verus! {
pub fn main_test() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    assert(SIZEOF_FRAME == core::mem::size_of::<Frame>());

    let tracked (
        Tracked(instance),
        Tracked(frames_token),
        Tracked(unused_addrs),
        Tracked(mut pte_token),
        Tracked(unused_pte_addrs),
    ) = SimplePageTable::Instance::initialize();
    let tracked mut unused_addrs = unused_addrs.into_map();
    let tracked mut unused_pte_addrs = unused_pte_addrs.into_map();

    let mut fake = MockPageTable {
        mem: alloc_page_table_entries(),
        frames: Tracked(frames_token),
        instance: Tracked(instance.clone()),
    };

    assert(fake.wf());

    let (p_root, Tracked(mut pt_root)) = get_from_index(1, &fake.mem); // TODO: permission violation?

    assert(pt_root.pptr() == p_root);
    assert(pt_root.mem_contents() == MemContents::<Frame>::Uninit);
    assert(p_root.addr() + SIZEOF_FRAME == fake.mem@[2].0.addr());
    assert(p_root.addr() == PHYSICAL_BASE_ADDRESS() + SIZEOF_FRAME as int);

    let mut f1 = Frame {
        // pa: p_root.addr(),
        ptes: [PageTableEntry {
            frame_pa: 0,
            flags: PteFlag,
            level: 0,
        }; NR_ENTRIES],
    };

    assert(unused_addrs.dom().contains(p_root.addr() as int));
    let tracked used_addr = unused_addrs.tracked_remove(p_root.addr() as int);

    assert(fake.wf());
    p_root.write(Tracked(&mut pt_root), f1);
    assert(fake.mem.len() == NR_ENTRIES);
    assert(fake.mem@.dom().contains(1));
    assert(fake.mem@.contains_key(1));

    fake.mem.remove(&1);
    assert(fake.mem.len() == NR_ENTRIES - 1);
    fake.mem.insert(1, (p_root, Tracked(pt_root)));
    assert(fake.mem.len() == NR_ENTRIES);

    // assert(!fake.wf()); // it seems we cannot assert the structure is not wf when it is not

    proof{
        assert(fake.frames@.value().dom().len() == 0);
        assert(!fake.frames@.value().dom().contains(p_root.addr() as int));

        // instance.new_at(p_root.addr(), f1, fake.frames.borrow_mut(), used_addr);
        instance.new_at(p_root.addr() as int, FrameView {
            pa: p_root.addr() as int,
            // has_ptes: false,
            pte_addrs: Seq::empty(),
        }, fake.frames.borrow_mut(), used_addr, &pte_token);

        assert(fake.frames@.value().contains_key(p_root.addr() as int));
    }
    assert(fake.frames@.value().contains_key(p_root.addr() as int));
    assert(p_root.addr() == fake.frames@.value()[p_root.addr() as int].pa);

    assert(fake.wf());

    let (p_f2, Tracked(mut pt_f2)) = get_from_index(2, &fake.mem);

    assert(pt_f2.pptr().addr() == p_root.addr() + SIZEOF_FRAME);
    let f2 = Frame {
        // pa: p_f2.addr(),
        ptes: [PageTableEntry {
            frame_pa: 0,
            flags: PteFlag,
            level: 0,
        }; NR_ENTRIES],
    };

    assert(unused_addrs.dom().contains(p_f2.addr() as int));
    let tracked used_addr = unused_addrs.tracked_remove(p_f2.addr() as int);

    proof{
        assert(fake.frames@.value().dom().len() == 1);
        assert(fake.frames@.value().dom().contains(p_root.addr() as int));
        assert(!fake.frames@.value().dom().contains(p_f2.addr() as int));

        // instance.new_at(p_f2.addr(), f2, fake.frames.borrow_mut(), used_addr);
        instance.new_at(p_f2.addr() as int, FrameView{
            pa: p_f2.addr() as int,
            // has_ptes: false,
            pte_addrs: Seq::empty(),
        }, fake.frames.borrow_mut(), used_addr, &pte_token);
    }

    p_f2.write(Tracked(&mut pt_f2), f2);
    // assert(fake.wf());

    let index = 10;
    let level = 4;
    let f1 = Frame {
        // pa: p_root.addr(),
        ptes: {
            let mut ptes = [PageTableEntry {
                frame_pa: 0,
                flags: PteFlag,
                level: 0,
            }; NR_ENTRIES];
            ptes[index] = PageTableEntry {
                frame_pa: p_f2.addr(),
                flags: PteFlag,
                level: level,
            };
            ptes
        }
    };
    let pte_addr = p_root.addr() + index * SIZEOF_PAGETABLEENTRY;

    let tracked pte_addr = unused_pte_addrs.tracked_remove(pte_addr as int);

    let (p_root, Tracked(mut pt_root)) = get_from_index(1, &fake.mem); // TODO: permission violation?
    p_root.write(Tracked(&mut pt_root), f1);
    proof{
        assert(fake.frames@.value().contains_key(p_root.addr() as int));
        assert(fake.frames@.value().contains_key(p_f2.addr() as int));
        instance.set_child(p_root.addr() as int, index, p_f2.addr() as int, level, fake.frames.borrow_mut(),
                                &mut pte_token, pte_addr);
    }
    fake.mem.remove(&1);
    assert(fake.mem.len() == NR_ENTRIES - 1);
    fake.mem.insert(1, (p_root, Tracked(pt_root)));

    assert(fake.wf());

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
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            (#[trigger] res@[i]).1@.pptr() == res@[i].0
        },
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            #[trigger] res@[i].1@.mem_contents() == MemContents::<Frame>::Uninit
        },
        forall |i:usize, j:usize| 0 <= i < j < NR_ENTRIES && i == j - 1 ==> {
            && (#[trigger] res@[i]).0.addr() + SIZEOF_FRAME == (#[trigger] res@[j]).0.addr() // pointers are adjacent
        },
        res@[0].0.addr() == PHYSICAL_BASE_ADDRESS_SPEC(),
        res@.dom().finite(),
{
    let mut map = HashMap::<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>::new();
    // map.insert(0, (PPtr::from_addr(0), Tracked::assume_new()));
    let p = PHYSICAL_BASE_ADDRESS();
    for i in 0..Paddr::MAX {
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
        forall |i:usize| 0 <= i < NR_ENTRIES ==> {
            (#[trigger] map@[i]).1@.pptr() == map@[i].0
        }
    ensures
        // res.0.addr() != 0,
        res.1@.pptr() == res.0,
        // NOTE: this is not true! && res.0.addr() == map@[index]@.0.addr()
        res.0 == map@[index].0,
        res.1 == map@[index].1
{
    let (p, Tracked(pt)) = map.get(&index).unwrap();
    (*p, Tracked::assume_new())
}

pub open spec fn index_to_addr(index: usize) -> usize {
    (PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) as usize
}

// TODO: can we eliminate division
pub open spec fn addr_to_index(addr: usize) -> usize {
    ((addr - PHYSICAL_BASE_ADDRESS_SPEC()) / SIZEOF_FRAME as int) as usize
}

pub open spec fn PHYSICAL_BASE_ADDRESS_SPEC() -> usize {
    0x1000
}

#[allow(unused_imports)]
use std::alloc::{alloc, dealloc, Layout};

#[verifier::external_body]
#[verifier::when_used_as_spec(PHYSICAL_BASE_ADDRESS_SPEC)]
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
    println!("spec::simple_page_table::main_test start.");
    // print 1
    let (p, Tracked(mut pt)) = mem.get(&1).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("Frame1: pa: {}", p.addr());

    println!("Frame1 10th pte points to: {}", frame.ptes[10].frame_pa);

    // print 2
    let (p, Tracked(mut pt)) = mem.get(&2).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("Frame2: pa: {}", p.addr());

    // let's try to find frame2 by virtual address
    let va = 10; // va is just the level since we only set one level of page table
    let (p, Tracked(mut pt)) = mem.get(&1).unwrap(); // let say root is 1
    let frame = p.read(Tracked(&mut pt));
    let pte = frame.ptes[va];
    let p2_addr = pte.frame_pa;
    let p2_index = (p2_addr - mem.get(&0).unwrap().0.addr()) / SIZEOF_FRAME as usize;
    let (p, Tracked(mut pt)) = mem.get(&p2_index).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("Frame2: pa: {}", p.addr());

    println!("spec::simple_page_table::main_test end.");
    println!();
}

} // verus!
