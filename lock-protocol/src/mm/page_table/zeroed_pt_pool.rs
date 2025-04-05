use std::sync::atomic::Ordering;

use vstd::prelude::verus;

use crate::{mm::{meta::AnyFrameMeta, PageTableLockTrait}, task::DisabledPreemptGuard};

use super::{
    node::{MapTrackingStatus, PageTableLock, PageTableNode, PageTablePageMeta},
    PageTableEntryTrait, PagingConstsTrait, PagingLevel,
};

verus! {

const POOL_SIZE: usize = 12; // TODO: fix POOL_SIZE

// TODO: zeroed_pt_pool::alloc() is not implemented yet.
pub(super) fn alloc<E: PageTableEntryTrait, C: PagingConstsTrait>(
    preempt_guard: &DisabledPreemptGuard,
    level: PagingLevel,
    is_tracked: MapTrackingStatus,
) -> PageTableLock<E, C> {
    // let cpu = preempt_guard.current_cpu();
    // let pool_size = POOL_SIZE.get_on_cpu(cpu);


    // let size = pool_size.load(Ordering::Relaxed);

    // if size == 0 {
        return PageTableLock::alloc(level, is_tracked);
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
}

}
