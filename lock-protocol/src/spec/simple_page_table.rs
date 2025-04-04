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
pub struct PageTableEntry {
    pub frame_pa: Paddr,
    pub flags: PteFlag,

    pub level: usize, // TODO: should this be here?
}

#[derive(Clone, Copy)]
pub struct Frame {
    // pub pa: Paddr,
    pub ptes: [PageTableEntry; 512],
    // pub has_ptes: bool,
}

pub ghost struct FrameView {
    pub pa: Paddr,
    // pub ptes: [PageTableEntry; 512],
    pub pte_addrs: Seq<Paddr>,
}

tokenized_state_machine!{
PageTable {

    fields {
        #[sharding(variable)]
        pub frames: Map<Paddr, FrameView>,

        #[sharding(set)]
        pub unused_addrs: Set<Paddr>,

        #[sharding(variable)]
        pub ptes: Map<Paddr, PageTableEntry>,

        #[sharding(set)]
        pub unused_pte_addrs: Set<Paddr>,
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
        new_at(addr: Paddr, newFrame: FrameView) {
            require addr != 0;
            require addr == newFrame.pa;
            // require forall |i: int| 0 <= i < NR_ENTRIES ==> #[trigger] newFrame.ptes[i].frame_pa == 0;
            require newFrame.pte_addrs.len() == 0;
            require forall |i: int| 0 <= i < NR_ENTRIES ==>
                !#[trigger]pre.ptes.dom().contains((newFrame.pa + i * SIZEOF_PAGETABLEENTRY) as usize);
            remove unused_addrs -= set { addr };

            update frames = pre.frames.insert(addr, newFrame);
        }
    }

    transition! {
        // set child relationship
        set_child(parent: Paddr, index: usize, child: Paddr, level: usize) {
            require pre.frames.contains_key(parent);
            require pre.frames.contains_key(child);
            require pre.frames[parent].pa != pre.frames[child].pa;
            require pre.frames[parent].pa == parent;
            // require pre.frames[child].level == pre.frames[parent].level + 1;
            require pre.frames[child].pa == child;
            let pte_addr = pre.frames[parent].pa + index * SIZEOF_PAGETABLEENTRY;
            require !pre.frames[parent].pte_addrs.contains(pte_addr as usize);
            require !pre.ptes.dom().contains(pte_addr as usize);

            update frames = pre.frames.insert(parent, FrameView {
                pa: pre.frames[parent].pa,
                pte_addrs: pre.frames[parent].pte_addrs.push(pte_addr as Paddr),
            });

            remove unused_pte_addrs -= set { pte_addr as Paddr };

            update ptes = pre.ptes.insert(
                pte_addr as usize,
                PageTableEntry {
                    frame_pa: child,
                    flags: PteFlag,
                    level: level,
                }
            );
        }
    }

    #[inductive(set_child)]
    fn tr_set_child_invariant(pre: Self, post: Self, parent: Paddr, index: usize, child: Paddr, level: usize) {
    }

    #[inductive(new_at)]
    fn tr_new_at_invariant(pre: Self, post: Self, addr: Paddr, newFrame: FrameView) {
        assert(!pre.frames.contains_key(addr));
        assert(pre.unused_addrs.contains(addr));
        assert(post.frames.contains_key(addr));
        assert(post.frames[addr] == newFrame);
        assert(!post.unused_addrs.contains(addr));
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[invariant]
    pub spec fn page_wf(self) -> bool {
        forall |addr: Paddr| 0 <= addr <= usize::MAX ==> {
            if (#[trigger] self.frames.dom().contains(addr)) {
                let node = #[trigger] self.frames[addr];
                node.pa == addr
                &&
                forall |i: int|
                #![trigger node.pte_addrs[i]]
                0 <= i < node.pte_addrs.len() ==>
                {
                    let pte_addr = node.pte_addrs[i];
                    if (self.ptes.dom().contains(pte_addr)) {
                        let pte = self.ptes[pte_addr];
                        self.frames.dom().contains(pte.frame_pa)
                        &&
                        self.frames[pte.frame_pa].pa == pte.frame_pa
                    } else {
                        true
                    }
                }
            } else {
                self.unused_addrs.contains(addr)
            }
        }
    }

    #[invariant]
    pub closed spec fn unused_addrs_are_not_in_frames(&self) -> bool {
        forall |addr: Paddr|
            #![trigger self.unused_addrs.contains(addr)]
            #![trigger self.frames.dom().contains(addr)]
            self.unused_addrs.contains(addr)
              <==> !self.frames.dom().contains(addr)
        &&
        forall |addr: Paddr|
            #![trigger self.ptes.dom().contains(addr)]
            #![trigger self.unused_pte_addrs.contains(addr)]
            self.unused_pte_addrs.contains(addr)
              <==> !self.ptes.dom().contains(addr)
    }

    // #[invariant]
    // pub closed spec fn unused_frames_are_not_child_of_frames(&self) -> bool {
    //     forall |addr: Paddr|
    //         #![trigger self.unused_addrs.contains(addr)]
    //         self.unused_addrs.contains(addr) && addr != 0 && !self.frames.dom().contains(addr)
    //             ==> forall |parent: Paddr|
    //                 #![trigger self.frames[parent]]
    //                 #![trigger self.frames.dom().contains(parent)]
    //                 self.frames.dom().contains(parent) ==>
    //                 forall |i: int| 0 <= i < NR_ENTRIES ==> {
    //                     let pte = #[trigger] self.frames[parent].ptes[i];
    //                     if (pte.frame_pa != 0) {
    //                         pte.frame_pa != addr
    //                         &&
    //                         !self.unused_addrs.contains(pte.frame_pa)
    //                     } else {
    //                         true
    //                     }
    //                 }
    // }

}
} // tokenized_state_machine

struct_with_invariants!{
    pub struct MockPageTable {
        pub mem: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>,
        pub frames: Tracked<PageTable::frames>,
        pub instance: Tracked<PageTable::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.frames@.instance_id() == self.instance@.id()
            &&
            self.mem.len() == NR_ENTRIES
            &&
            forall |i: usize, j: usize| 0 < i < NR_ENTRIES && j == index_to_addr(i) ==>
                if (self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
                    self.frames@.value().contains_key(j)
                    &&
                    #[trigger] self.frames@.value()[j].pa == #[trigger] self.mem@[i].0.addr()
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

pub fn main() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    assert(SIZEOF_FRAME == core::mem::size_of::<Frame>());

    let tracked (
        Tracked(instance),
        Tracked(frames_token),
        Tracked(unused_addrs),
        Tracked(mut pte_token),
        Tracked(unused_pte_addrs),
    ) = PageTable::Instance::initialize();
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

    let mut f1 = Frame {
        // pa: p_root.addr(),
        ptes: [PageTableEntry {
            frame_pa: 0,
            flags: PteFlag,
            level: 0,
        }; NR_ENTRIES],
    };

    assert(unused_addrs.dom().contains(p_root.addr()));
    let tracked used_addr = unused_addrs.tracked_remove(p_root.addr());

    proof{
        assert(fake.frames@.value().dom().len() == 0);
        assert(!fake.frames@.value().dom().contains(p_root.addr()));

        // instance.new_at(p_root.addr(), f1, fake.frames.borrow_mut(), used_addr);
        instance.new_at(p_root.addr(), FrameView {
            pa: p_root.addr(),
            // has_ptes: false,
            pte_addrs: Seq::empty(),
        }, fake.frames.borrow_mut(), used_addr, &pte_token);

        assert(fake.frames@.value().contains_key(p_root.addr()));
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
        // pa: p_f2.addr(),
        ptes: [PageTableEntry {
            frame_pa: 0,
            flags: PteFlag,
            level: 0,
        }; NR_ENTRIES],
    };

    assert(unused_addrs.dom().contains(p_f2.addr()));
    let tracked used_addr = unused_addrs.tracked_remove(p_f2.addr());

    proof{
        assert(fake.frames@.value().dom().len() == 1);
        assert(fake.frames@.value().dom().contains(p_root.addr()));
        assert(!fake.frames@.value().dom().contains(p_f2.addr()));

        // instance.new_at(p_f2.addr(), f2, fake.frames.borrow_mut(), used_addr);
        instance.new_at(p_f2.addr(), FrameView{
            pa: p_f2.addr(),
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

    let tracked pte_addr = unused_pte_addrs.tracked_remove(pte_addr as usize);

    let (p_root, Tracked(mut pt_root)) = get_from_index(1, &fake.mem); // TODO: permission violation?
    p_root.write(Tracked(&mut pt_root), f1);
    proof{
        assert(fake.frames@.value().contains_key(p_root.addr()));
        assert(fake.frames@.value().contains_key(p_f2.addr()));
        // set_child(parent: Paddr, index: usize, child: Paddr, level: usize)
        // provide the arguments: provide the arguments: `(
        //         /* usize */, /* usize */, /* usize */, /* usize */,
        //         /* &mut spec::simple_page_table::PageTable::frames */,
        //         /* &mut spec::simple_page_table::PageTable::ptes */,
        //         /* spec::simple_page_table::PageTable::unused_pte_addrs */)`
        instance.set_child(p_root.addr(), index, p_f2.addr(), level, fake.frames.borrow_mut(),
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
        res@[0].0.addr() == 0,
        res@[1].0.addr() == PHYSICAL_BASE_ADDRESS_SPEC(), // points to the hardware page table
        res@.dom().finite(),
{
    let mut map = HashMap::<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>::new();
    // map.insert(0, (PPtr::from_addr(0), Tracked::assume_new()));
    let p = PHYSICAL_BASE_ADDRESS();
    for i in 0..NR_ENTRIES {
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
}

} // verus!
