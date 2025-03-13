//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
extern crate vstd_extra;
use vstd::prelude::*;
use vstd::cell::*;
use vstd::atomic::*;
use vstd::atomic_ghost::*;
use crate::common::*;
use aster_common::prelude::*;

verus!{

//
// # Primitives for MetaSlot
//

impl MetaSlot {

#[rustc_allow_incoherent_impl]
#[verifier::external_body]
pub fn as_meta_slot_ptr(&self) -> (res: Vaddr)
    ensures
        res as int == self.id(),
{
    self as *const MetaSlot as Vaddr
}

}

}

