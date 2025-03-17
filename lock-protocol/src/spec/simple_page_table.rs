use std::borrow::BorrowMut;
use std::intrinsics::size_of;

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::cell::*;
use vstd::hash_map::*;
use vstd::tokens::MapToken;
use vstd::raw_ptr::*;
use vstd::simple_pptr::*;
use vstd::simple_pptr::PointsTo;

use crate::Vaddr;
use crate::Paddr;
use crate::NR_ENTRIES;
verus! {

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub pa: Paddr,
    pub flags: PteFlag,

    pub level: usize, // this should not be here, just for testing
    pub children: Paddr, // this should not be here, just for testing
    pub children_index: usize, // this should not be here, just for testing
}

tokenized_state_machine!{
PageTable {

    fields {
        #[sharding(map)]
        pub pages: Map<Paddr, PageTableEntry>,
    }

    init!{
        initialize() {
            init pages = Map::new(|p: Paddr| 0 <= p <= NR_ENTRIES, |p: Paddr| PageTableEntry {
                pa: p,
                flags: PteFlag,

                level: 0,
                children: 0,
                children_index: 0,
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

#[verifier::external_body]
fn alloc_page_table_entries() -> (res: HashMapWithView<usize, Tracked<(PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>)>>)
    ensures
        res.len() == 1000
        && forall|i:usize| 0 <= i < 999 ==>
            (#[trigger] res@[i])@.1@.pptr() == res@[i]@.0
            && res@[i]@.1@.mem_contents() == MemContents::<PageTableEntry>::Uninit
            && res@[i]@.0.addr() + core::mem::size_of::<PageTableEntry>() == res@[((i + 1) as usize)]@.0.addr() // pointers are adjacent
            // && res[i].0.addr() == 0x1000 // points to the hardware page table
{
    unimplemented!()
}

#[verifier::external_body]
fn get_from_index(index: usize, map: &HashMapWithView<usize, Tracked<(PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>)>>) -> (res: (PPtr<PageTableEntry>, Tracked<PointsTo<PageTableEntry>>))
    ensures
        res.1@.pptr() == res.0
        && res.1@.mem_contents() == MemContents::<PageTableEntry>::Uninit
        && res.0.addr() + core::mem::size_of::<PageTableEntry>() == map@[((index + 1) as usize)]@.0.addr() // pointers are adjacent
        // && res[i].0.addr() == 0x1000 // points to the hardware page table
{
    unimplemented!()
}

fn main() {
    let tracked (Tracked(instance), Tracked(pages)) = PageTable::Instance::initialize();

    let mut mem = alloc_page_table_entries();

    let (p_root, Tracked(mut pt_root)) = get_from_index(0, &mem);
    assert(pt_root.pptr() == p_root);
    assert(pt_root.mem_contents() == MemContents::<PageTableEntry>::Uninit);
    // assert(root.addr() + size_of::<PageTableEntry>() == mem@[1]@.0.addr());

    let pte1 = PageTableEntry {
        pa: p_root.addr(),
        flags: PteFlag,
        level: 0,
        children: p_root.addr() + core::mem::size_of::<PageTableEntry>(),
        children_index: 1,
    };

    proof{
        // instance.new_at(p_root.addr(), pte1, pages.into_map().index(p_root.addr()));
    }

    p_root.write(Tracked(&mut pt_root), pte1);

    let (p_pte2, Tracked(mut pt_pte2)) = get_from_index(1, &mem);
    let pte2 = PageTableEntry {
        pa: p_root.addr() + core::mem::size_of::<PageTableEntry>(),
        flags: PteFlag,
        level: 1,
        children: 0,
        children_index: 0,
    };

    p_pte2.write(Tracked(&mut pt_pte2), pte2);

    proof{
        // assert(forall|i:usize| 0 <= i < 1000 ==> {
        //     let (p, Tracked(mut pt)) = get_from_index(i, &mem);
        //     if (p.borrow(Tracked(&mut pt)).children != 0)
        //     {
        //         let (p2, Tracked(mut pt2)) = get_from_index(p.borrow(Tracked(&mut pt)).children_index, &mem);
        //         p.borrow(Tracked(&mut pt)).children == p2.borrow(Tracked(&mut pt2)).pa
        //     } else {
        //         true
        //     }}
        // );
    }

}

} // verus!
