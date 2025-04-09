use std::sync::atomic::Ordering;

use vstd::prelude::*;

use crate::{mm::{meta::AnyFrameMeta, PageTableLockTrait}, task::DisabledPreemptGuard};

use super::{
    node::{MapTrackingStatus, PageTableNode, PageTablePageMeta},
    PageTableEntryTrait, PagingConstsTrait, PagingLevel,
};

use crate::exec;
use crate::spec::simple_page_table;
use vstd::tokens::*;

verus! {

const POOL_SIZE: usize = 12; // TODO: fix POOL_SIZE

// TODO: zeroed_pt_pool::alloc() is not implemented yet.
pub(super) fn alloc<E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>>(
    preempt_guard: &DisabledPreemptGuard,
    level: PagingLevel,
    is_tracked: MapTrackingStatus,

    mpt: &mut exec::MockPageTable,
    instance: Tracked<simple_page_table::SimplePageTable::Instance>,
    cur_alloc_index: usize,
    used_addr: usize,
    used_addr_token: Tracked<simple_page_table::SimplePageTable::unused_addrs>,
    // tokens: Tracked<exec::Tokens>
) -> (res: PTL)
requires
    old(mpt).wf(),
    old(mpt).ptes@.instance_id() == instance@.id(),
    old(mpt).frames@.instance_id() == instance@.id(),
    cur_alloc_index < exec::MAX_FRAME_NUM,
    used_addr_token@.instance_id() == instance@.id(),
    // used_addr_token@.element() == used_addr,
    used_addr == (cur_alloc_index * exec::SIZEOF_FRAME as usize) + exec::PHYSICAL_BASE_ADDRESS(),
ensures
    mpt.wf(),
    mpt.ptes@.instance_id() == instance@.id(),
    mpt.frames@.instance_id() == instance@.id(),
    res.paddr() == used_addr as usize,
{
    // let cpu = preempt_guard.current_cpu();
    // let pool_size = POOL_SIZE.get_on_cpu(cpu);


    // let size = pool_size.load(Ordering::Relaxed);

    // if size == 0 {
        // return PageTableLock::alloc(level, is_tracked);
    // }
    // let irq_guard = crate::trap::disable_local();
    // let pool_deref_guard = ZEROED_PT_POOL.get_with(&irq_guard);
    // let mut pool = pool_deref_guard.borrow_mut();
    // let frame = pool[size - 1].take().unwrap();
    // pool_size.store(size - 1, Ordering::Relaxed);

    // let frame: PageTableNode<E, C> = frame
    //     .repurpose(PageTablePageMeta::<E, C>::new_locked(level, is_tracked))
    //     .into();

    // // SAFETY: The metadata must match the locked frame.
    // unsafe { PageTableLock::from_raw_paddr(frame.into_raw()) }

    PTL::alloc(level, is_tracked, mpt, instance, cur_alloc_index, used_addr, used_addr_token)
}

}
