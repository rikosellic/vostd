use vstd::prelude::*;

use aster_common::prelude::*;
use vstd_extra::ownership::*;

verus! {

impl<C: PageTableConfig> Child<C> {

    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_spec(self, slot_own : &MetaSlotOwner,
                                        slot_perm : &vstd::simple_pptr::PointsTo<MetaSlot>) -> C::E {
        match self {
            Child::PageTable(node) => C::E::new_pt_spec(slot_perm.value().frame_paddr_spec(slot_own@)),
            Child::Frame(paddr, level, prop) => C::E::new_page_spec(paddr, level, prop),
            Child::None => C::E::new_absent_spec(),
        }
    }
}

}