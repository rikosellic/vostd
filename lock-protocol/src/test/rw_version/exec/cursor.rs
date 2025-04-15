use std::mem::ManuallyDrop;
use core::ops::Deref;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::atomic_with_ghost;
use vstd::rwlock::{
    ReadHandle,
    WriteHandle,
};
use vstd::vpanic;
use vstd::pervasive::allow_panic;

use super::super::spec::{
    common::*,
    utils::*,
    tree::*,
};
use super::{
    common::*,
    types::*,
    frame::*,
    page_table::*,
};

verus! {

#[is_variant]
pub enum GuardInPath<'a> {
    ReadLocked(ReadHandle<'a, NodeToken, spec_fn(NodeToken) -> bool>),
    WriteLocked(WriteHandle<'a, NodeToken, spec_fn(NodeToken) -> bool>),
    None,
}

struct_with_invariants!{

pub struct Cursor<'a> {
    pub path: Vec<GuardInPath<'a>>,
    pub level: Level,
    pub guard_level: Level,
    // pub va: Vaddr,
}

pub open spec fn wf(&self) -> bool {
    predicate {
        &&& self.path@.len() == 4

        &&& 1 <= self.level <= 4
        &&& 1 <= self.guard_level <= 4
        &&& self.level <= self.guard_level

        &&& forall |level: Level| #![trigger self.path[level - 1]] 
            1 <= level <= 4 ==> {
                if level < self.guard_level {
                    self.path[level - 1].is_None()
                } else if level == self.guard_level {
                    self.path[level - 1].is_WriteLocked()
                } else {
                    self.path[level - 1].is_ReadLocked()
                }
            }

        // &&& valid_vaddr(self.va)
        // &&& vaddr_is_aligned(self.va)
    }
}

}

impl<'a> Cursor<'a> {

    pub open spec fn inv_cur_nid(&self, nid: NodeId) -> bool {
        &&& self.guard_level as nat == NodeHelper::nid_to_level(nid)
        // &&& va_level_to_nid(self.va, self.level) == nid
    }

}

}

verus! {

pub fn lock_range<'a>(
    pt: &PageTable, 
    allocator: &'a mut FrameAllocator,
    // va: &Range<Vaddr>,
    nid: u64,
) -> (res: Cursor<'a>)
    requires
        pt.wf(*old(allocator)),
        old(allocator).wf(),
        NodeHelper::valid_nid(nid as NodeId),
    ensures
        allocator.wf(),
        res.wf(),
        res.inv_cur_nid(nid as NodeId),
        res.level == res.guard_level,
{
    let mut path: Vec<GuardInPath<'a>> = Vec::with_capacity(4);
    for i in 0..4
        invariant
            0 <= i <= 4,
            path@.len() == i,
            forall |_i| 0 <= _i < i ==> path@[_i].is_None(),
    {
        path.push(GuardInPath::None);
    }
    assert(path.len() == 4);
    assert(forall |i| 0 <= i < 4 ==> path@[i].is_None());

    let mut cur_nid: u64 = 0;
    let mut cur_level: Level = 4;

    while cur_nid != nid
        invariant
            pt.wf(*allocator),
            allocator.wf(),

            NodeHelper::valid_nid(cur_nid as NodeId),
            NodeHelper::valid_nid(nid as NodeId),
            NodeHelper::in_subtree(cur_nid as NodeId, nid as NodeId),
            1 <= cur_level <= 4,
            cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId),

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            forall |i| 0 <= i < cur_level ==> path@[i].is_None(),
    {
        let pa: Paddr = atomic_with_ghost!{
            pt.nodes[cur_nid as usize] => load();
            returning res;
            ghost g => {
                assert(g.nid == cur_nid as NodeId);
                if res != INVALID_PADDR {
                    assert(g.tokens.is_None());
                }
            }
        };

        // TODO: fix this.
        if pa == INVALID_PADDR { continue; }

        assert(valid_paddr(pa));
        assert(paddr_is_aligned(pa));

        assert(allocator.usages@[pa_to_fid(pa) as int].is_PageTable()) by { admit(); };
        let frame: &Frame = allocator.get_pt_frame_from_pa(pa);

        let read_handle = unsafe {
            frame.page_table_frame.deref().rw_lock.acquire_read()
        };
        // path[(cur_level - 1) as usize] = GuardInPath::ReadLocked(read_handle);

        // #[verifier::loop_isolation(false)]
        // for offset in 0..512
        // {
        //     assert(valid_pte_offset(offset as nat));

        // }
        // cur_level = cur_level - 1;
    }
    assert(nid == cur_nid);
    assert(cur_level == NodeHelper::nid_to_level(nid as NodeId));

    loop
        invariant_except_break
            pt.wf(*allocator),
            allocator.wf(),

            NodeHelper::valid_nid(nid as NodeId),
            1 <= cur_level <= 4,
            cur_level as nat == NodeHelper::nid_to_level(nid as NodeId),

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            forall |i| 0 <= i < cur_level ==> path@[i].is_None(),
        ensures
            pt.wf(*allocator),
            allocator.wf(),

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            path@[cur_level - 1].is_WriteLocked(),
            forall |i| 0 <= i < cur_level - 1 ==> path@[i].is_None(),
    {
        let pa: Paddr = atomic_with_ghost!{
            pt.nodes[nid as usize] => load();
            returning res;
            ghost g => {
                assert(g.nid == nid as NodeId);
                if res != INVALID_PADDR {
                    assert(g.tokens.is_None());
                }
            }
        };

        // TODO: fix this.
        if pa == INVALID_PADDR { continue; }

        assert(valid_paddr(pa));
        assert(paddr_is_aligned(pa));

        assert(allocator.usages@[pa_to_fid(pa) as int].is_PageTable()) by { admit(); };
        let frame: &Frame = allocator.get_pt_frame_from_pa(pa);

        let (token, write_handle) = unsafe {
            frame.page_table_frame.deref().rw_lock.acquire_write()
        };
        assert(cur_level >= 1);
        path[(cur_level - 1) as usize] = GuardInPath::WriteLocked(write_handle);
        // pt.inst.borrow().write_lock()

        break;
    }

    let cursor = Cursor::<'a> {
        path,
        level: cur_level,
        guard_level: cur_level,
    };

    cursor
}

}