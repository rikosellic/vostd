use crate::mm::{
    meta::AnyFrameMeta, MapTrackingStatus, PageTable, PageTableEntryTrait, PageTableMode,
    PagingConstsTrait, Vaddr,
};
use std::ops::Range;

use super::Cursor;

#[verifier::external_body]
pub fn lock_range<
    'a,
    M: PageTableMode,
    // E: PageTableEntryTrait = PageTableEntry,
    E: PageTableEntryTrait,
    // C: PagingConstsTrait = PagingConsts,
    C: PagingConstsTrait,
>(
    pt: &PageTable<M, E, C>,
    va: &Range<Vaddr>,
    new_pt_is_tracked: MapTrackingStatus,
) -> Cursor<'a, M, E, C> {
    // Placeholder implementation
    unimplemented!()
}
