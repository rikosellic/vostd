use vstd::{prelude::*, simple_pptr::PPtr};
use std::collections::HashMap;

use crate::mm::entry::Entry;
use crate::mm::page_table::PageTableNode;

use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTableLock, PageTableLockTrait,
        PageTablePageMeta, PagingConsts, PagingConstsTrait, UserMode, Vaddr, MAX_USERSPACE_VADDR,
        NR_LEVELS, PAGE_SIZE,
    },
    spec::simple_page_table,
    task::{disable_preempt, DisabledPreemptGuard},
};

verus! {

// TODO: This is a mock implementation of the page table entry. It should be replaced with the actual implementation, e.g., x86_64.
#[derive(Copy, Clone)]
pub struct SimplePageTableEntry {}

impl PageTableEntryTrait for SimplePageTableEntry {
    #[verifier::external_body]
    fn is_present(&self) -> bool {
        unimplemented!()
    }

    #[verifier::external_body]
    fn paddr(&self) -> usize {
        unimplemented!()
    }

    #[verifier::external_body]
    fn is_last(&self, level: u8) -> bool {
        unimplemented!()
    }

    #[verifier::external_body]
    fn new_page(paddr: crate::mm::Paddr, level: crate::mm::PagingLevel, prop: crate::mm::page_prop::PageProperty) -> Self {
        todo!()
    }

    #[verifier::external_body]
    fn new_pt(paddr: crate::mm::Paddr) -> Self {
        todo!()
    }

    #[verifier::external_body]
    fn new_token(token: crate::mm::vm_space::Token) -> Self {
        todo!()
    }

    #[verifier::external_body]
    fn prop(&self) -> crate::mm::page_prop::PageProperty {
        todo!()
    }

    #[verifier::external_body]
    fn set_prop(&mut self, prop: crate::mm::page_prop::PageProperty) {
        todo!()
    }

    #[verifier::external_body]
    fn set_paddr(&mut self, paddr: crate::mm::Paddr) {
        todo!()
    }

    #[verifier::external_body]
    fn new_absent() -> Self {
        // Self::default()
        std::unimplemented!()
    }

    #[verifier::external_body]
    fn as_usize(self) -> usize {
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        // unsafe { transmute_unchecked(self) }
        // TODO: Implement this function
        std::unimplemented!()
    }

    #[verifier::external_body]
    fn from_usize(pte_raw: usize) -> Self {
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        // unsafe { transmute_unchecked(pte_raw) }
        // TODO: Implement this function
        std::unimplemented!()
    }
}

pub struct SimpleFrameMeta {}

impl AnyFrameMeta for SimpleFrameMeta {
}

// TODO: This FakePageTableLock will ignore Entry and MetaSlot. We possibly need to use PageTableNode later.
pub struct FakePageTableLock<E: PageTableEntryTrait, C: PagingConstsTrait> {
    pub phantom: std::marker::PhantomData<(E, C)>,
}

impl<E: PageTableEntryTrait, C: PagingConstsTrait> PageTableLockTrait<E, C> for FakePageTableLock<E, C> {

    // #[verifier::external_body]
    // fn entry(&self, idx: usize) -> crate::mm::entry::Entry<'_, E, C, Self> {
    //     Entry::new_at(self, idx)
    // }

    #[verifier::external_body]
    fn paddr(&self) -> crate::mm::Paddr {
        todo!()
    }

    #[verifier::external_body]
    fn alloc(level: crate::mm::PagingLevel, is_tracked: crate::mm::MapTrackingStatus) -> Self where Self: Sized {
        todo!()
    }

    #[verifier::external_body]
    fn unlock(&mut self) -> PageTableNode<E, C> {
        todo!()
    }

    #[verifier::external_body]
    fn into_raw_paddr(self: Self) -> crate::mm::Paddr where Self: Sized {
        todo!()
    }

    #[verifier::external_body]
    fn from_raw_paddr(paddr: crate::mm::Paddr) -> Self where Self: Sized {
        todo!()
    }

    #[verifier::external_body]
    fn nr_children(&self) -> u16 {
        todo!()
    }

    #[verifier::external_body]
    fn read_pte(&self, idx: usize) -> E {
        todo!()
    }

    #[verifier::external_body]
    fn write_pte(&self, idx: usize, pte: E) {
        todo!()
    }

    #[verifier::external_body]
    fn meta(&self) -> &PageTablePageMeta<E, C> {
        todo!()
    }

    // #[verifier::external_body]
    // fn nr_children_mut(&mut self) -> &mut u16 {
    //     todo!()
    // }

    #[verifier::external_body]
    fn change_children(&self, delta: i16) {
        todo!()
    }
    
    #[verifier::external_body]
    fn is_tracked(&self) -> crate::mm::MapTrackingStatus {
        todo!()
    }

}

struct_with_invariants!{
    pub struct MockPageTable {
        // pub mem: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>,
        // pub frames: Tracked<PageTable::frames>,
        // pub instance: Tracked<PageTable::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            // self.frames@.instance_id() == self.instance@.id()
            // &&
            // self.mem.len() == NR_ENTRIES
            // &&
            // forall |i: usize, j: usize| 0 < i < NR_ENTRIES && j == index_to_addr(i) ==>
            //     if (self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
            //         self.frames@.value().contains_key(j)
            //         &&
            //         #[trigger] self.frames@.value()[j].pa == #[trigger] self.mem@[i].0.addr()
            //     } else {
            //         true
            //     }

            // &&
            // forall |i: usize| 0 < i < NR_ENTRIES ==>
            //     if (#[trigger] self.mem@[i].1@.mem_contents() != MemContents::<Frame>::Uninit) {
            //         self.frames@.value().contains_key(self.mem@[i].0.addr())
            //         &&
            //         self.frames@.value()[self.mem@[i].0.addr()] == self.mem@[i].1@.value()
            //     } else {
            //         true
            //     }
            true
        }
    }
}

pub fn test_map(va: Vaddr, frame: Frame<SimpleFrameMeta>, page_prop: page_prop::PageProperty)
requires
    0 <= va < MAX_USERSPACE_VADDR,
{
    let tracked (
        Tracked(instance),
        Tracked(frames_token),
        Tracked(unused_addrs),
        Tracked(mut pte_token),
        Tracked(unused_pte_addrs),
    ) = simple_page_table::PageTable::Instance::initialize();

    // TODO: use Cursor::new
    let mut cursor =
    CursorMut::<UserMode, SimplePageTableEntry, PagingConsts, FakePageTableLock<SimplePageTableEntry, PagingConsts>> {
        0: Cursor::<UserMode, SimplePageTableEntry, PagingConsts, FakePageTableLock<SimplePageTableEntry, PagingConsts>> {
            path: Vec::new(),
            level: 4,
            guard_level: NR_LEVELS as u8,
            va: va,
            barrier_va: 0..MAX_USERSPACE_VADDR + PAGE_SIZE, // TODO: maybe cursor::new can solve this
            preempt_guard: disable_preempt(),
            _phantom: std::marker::PhantomData,
        }
    };

    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(Some(
        FakePageTableLock {
            phantom: std::marker::PhantomData,
        }
    ));

    assert(cursor.0.path.len() == NR_LEVELS as usize);
    assert(cursor.0.path[cursor.0.level as usize - 1].is_some());

    cursor.map::<SimpleFrameMeta>(frame, page_prop);

    assert(cursor.0.path.len() == NR_LEVELS as usize);
}

}
