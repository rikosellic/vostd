use std::{
    any::TypeId,
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    char::MAX,
    marker::PhantomData,
    ops::Range,
};

use vstd::simple_pptr::*;
use vstd::{invariant, layout::is_power_2, pervasive::VecAdditionalExecFns, prelude::*};
use vstd::bits::*;
use vstd::tokens::SetToken;

use crate::{
    helpers::align_ext::align_down,
    mm::{
        child::Child, entry::Entry, frame, meta::AnyFrameMeta, node::PageTableNode,
        nr_subpage_per_huge, page_prop::PageProperty, page_size, vm_space::Token, Frame,
        MapTrackingStatus, Paddr, PageTableLockTrait, Vaddr, MAX_USERSPACE_VADDR, NR_ENTRIES,
        PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::VMALLOC_VADDR_RANGE,
};

use super::{
    pte_index, KernelMode, PageTable, PageTableEntryTrait, PageTableError, PageTableMode,
    PagingConsts, PagingConstsTrait, PagingLevel, UserMode,
};

use crate::spec::simple_page_table;
use crate::exec;

verus! {

pub open spec fn level_is_greate_than_one(level: PagingLevel) -> bool {
    &&& level > 1
    &&& level <= PagingConsts::NR_LEVELS_SPEC()
}

pub open spec fn instance_match(mpt: &exec::MockPageTable,
                                tokens: Tracked<exec::Tokens>) -> bool {
    &&& forall |i| tokens@.unused_addrs.contains_key(i) ==>
            #[trigger] tokens@.unused_addrs[i].instance_id() == mpt.instance@.id()
    &&& forall |i| tokens@.unused_pte_addrs.contains_key(i) ==>
            #[trigger] tokens@.unused_pte_addrs[i].instance_id() == mpt.instance@.id()
}

pub open spec fn instance_match_addrs(mpt: &exec::MockPageTable,
                                      unused_addrs: Map<int, simple_page_table::SimplePageTable::unused_addrs>,
                                      unused_pte_addrs: Map<int, simple_page_table::SimplePageTable::unused_pte_addrs>,
                                     ) -> bool {
    &&& forall |i| unused_addrs.contains_key(i) ==>
            #[trigger] unused_addrs[i].instance_id() == mpt.instance@.id()
    &&& forall |i| unused_pte_addrs.contains_key(i) ==>
            #[trigger] unused_pte_addrs[i].instance_id() == mpt.instance@.id()
}

pub open spec fn path_index_at_level(level: PagingLevel) -> int {
    // level - 1
    level - 1
}

}
