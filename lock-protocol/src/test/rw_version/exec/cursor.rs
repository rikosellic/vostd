use std::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

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
    utils::*,
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
    pub va: Vaddr,
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

    pub open spec fn init_wf(&self, va: Range<Vaddr>) -> bool 
        recommends
            va_range_wf(va),
    {
        &&& self.level == self.guard_level
        &&& self.va == va.start
        &&& self.level == get_guard_level(va)
    }

}

}

verus! {

pub open spec fn va_range_wf(va: Range<Vaddr>) -> bool {
    &&& valid_va_range(va)
    &&& va.start < va.end
    &&& vaddr_is_aligned(va.start)
    &&& vaddr_is_aligned(va.end)
}

pub open spec fn get_level_rec(va: Range<Vaddr>, cur_level: Level) -> Level 
    recommends
        va_range_wf(va),
        1 <= cur_level <= 4,
    decreases cur_level,
{
    if 1 <= cur_level <= 4 {
        if cur_level == 1 { 1 }
        else {
            let st = va.start;
            let en = (va.end - 1) as u64;

            if va_level_to_offset(st, cur_level) == va_level_to_offset(en, cur_level) {
                get_level_rec(va, (cur_level - 1) as Level)
            } else { cur_level }
        }
    } else { arbitrary() }
}

pub open spec fn get_guard_level(va: Range<Vaddr>) -> Level
    recommends
        va_range_wf(va),
{
    get_level_rec(va, 4)
}

pub proof fn lemma_get_guard_level(va: Range<Vaddr>)
    requires
        va_range_wf(va),
    ensures
        1 <= get_guard_level(va) <= 4,
{
    admit();
}

pub fn lock_range<'a>(
    pt: &PageTable, 
    allocator: &'a mut FrameAllocator,
    va: &Range<Vaddr>,
) -> (res: Cursor<'a>)
    requires
        pt.wf(*old(allocator)),
        old(allocator).wf(),
        va_range_wf(*va),
    ensures
        pt.wf(*allocator),
        allocator.wf(),
        res.wf(),
        res.init_wf(*va),
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

    assert(cur_nid as NodeId == NodeHelper::root_id());
    assert(NodeHelper::valid_nid(cur_nid as NodeId)) by {
        NodeHelper::lemma_root_id();
    };
    proof {
        lemma_get_guard_level(*va);
    }
    while cur_level > 1
        invariant_except_break
            pt.wf(*allocator),
            allocator.wf(),
            va_range_wf(*va),

            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId),
            cur_level >= get_guard_level(*va),
            1 <= get_guard_level(*va) <= 4,

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            forall |i| 0 <= i < cur_level ==> path@[i].is_None(),
        ensures
            pt.wf(*allocator),
            allocator.wf(),
            va_range_wf(*va),

            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId),
            cur_level == get_guard_level(*va),

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            forall |i| 0 <= i < cur_level ==> path@[i].is_None(),
    {
        let start_idx = pte_index(va.start, cur_level);
        let level_too_high = {
            let end_idx = pte_index(va.end - 1, cur_level);
            cur_level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            assert(cur_level == get_guard_level(*va)) by { admit(); };
            break;
        }
        assert(cur_level != get_guard_level(*va)) by { admit(); };

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
        path[(cur_level - 1) as usize] = GuardInPath::ReadLocked(read_handle);

        assert(NodeHelper::is_not_leaf(cur_nid as NodeId)) by {
            assert(cur_level as nat == NodeHelper::nid_to_level(cur_nid as NodeId));
            assert(cur_level > 1);
            NodeHelper::lemma_level_dep_relation(cur_nid as NodeId);
        };
        let offset: u64 = pte_index(va.start, cur_level);
        cur_nid = NodeHelperExec::get_child_exec(cur_nid, offset);
        cur_level = cur_level - 1;
        assert(cur_nid as NodeId == va_level_to_nid(va.start, cur_level)) by { admit(); };
    }

    loop
        invariant_except_break
            pt.wf(*allocator),
            allocator.wf(),
            va_range_wf(*va),

            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level == get_guard_level(*va),

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            forall |i| 0 <= i < cur_level ==> path@[i].is_None(),
        ensures
            pt.wf(*allocator),
            allocator.wf(),

            NodeHelper::valid_nid(cur_nid as NodeId),
            cur_nid as NodeId == va_level_to_nid(va.start, cur_level),
            1 <= cur_level <= 4,
            cur_level == get_guard_level(*va),

            path.len() == 4,
            forall |i| cur_level <= i < 4 ==> path@[i].is_ReadLocked(),
            path@[cur_level - 1].is_WriteLocked(),
            forall |i| 0 <= i < cur_level - 1 ==> path@[i].is_None(),
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
        va: va.start,
    };

    cursor
}

}