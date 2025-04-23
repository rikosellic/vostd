use vstd::prelude::*;

use super::*;
use super::model::*;
use crate::common::*;

verus! {

impl MetaSlotModel {

pub open spec fn claim_spec(&self, slot: &MetaSlot,
    usage: PageUsage, ok: bool, m_end: &MetaSlotModel) -> bool
{
    usage != PageUsage::Unused &&
    slot.inv_relate(self) &&
    self.state == MetaSlotState::Unused ==> {
    &&& self.ref_count == m_end.ref_count
    &&& self.address == m_end.address
    &&& match ok {
        true => {
        &&& m_end.state == MetaSlotState::Claimed
        &&& m_end.usage == usage
        &&& m_end.inner_perm.is_some()
        &&& m_end.inner_perm.unwrap()@.id() == slot._inner.id()
        &&& m_end.inner_perm.unwrap()@.is_uninit()
        },
        false => {
        &&& m_end == self
        }
    }
    }
}

pub open spec fn inc0_spec(&self, rv: u32, m_end: &MetaSlotModel) -> bool
{
&&& rv == 0
&&& m_end.ref_count == self.ref_count + 1
&&& m_end.ref_count_perm@.view().patomic == self.ref_count_perm@.view().patomic
&&& m_end.ref_count_perm@.view().value == self.ref_count_perm@.view().value + 1
&&& m_end.address == self.address
&&& m_end.state == self.state
&&& m_end.usage == self.usage
&&& m_end.inner_perm == self.inner_perm
}


pub open spec fn inc_spec(&self, rv: u32, m_end: &MetaSlotModel) -> bool
{
    self.ref_count < u32::MAX ==> {
    &&& rv == self.ref_count
    &&& m_end.ref_count == self.ref_count + 1
    &&& m_end.ref_count_perm@.view().patomic == self.ref_count_perm@.view().patomic
    &&& m_end.ref_count_perm@.view().value == self.ref_count_perm@.view().value + 1
    &&& m_end.address == self.address
    &&& m_end.state == self.state
    &&& m_end.usage == self.usage
    &&& m_end.inner_perm == self.inner_perm
    }
}

pub open spec fn dec_spec(&self, rv: u32, m_end: &MetaSlotModel) -> bool
{
    self.ref_count > 0 &&
    self.state == MetaSlotState::Used ==> {
    &&& rv == self.ref_count
    &&& m_end.ref_count == self.ref_count - 1
    &&& m_end.ref_count_perm@.view().patomic == self.ref_count_perm@.view().patomic
    &&& m_end.ref_count_perm@.view().value == self.ref_count_perm@.view().value - 1
    &&& m_end.address == self.address
    &&& m_end.state == self.state
    &&& m_end.usage == self.usage
    &&& m_end.inner_perm == self.inner_perm
    }
}

pub open spec fn put_inner_spec(&self, inner: MetaSlotInner, m_end: &MetaSlotModel) -> bool
{
    self.state == MetaSlotState::Claimed ==> {
    &&& m_end.ref_count_perm == self.ref_count_perm
    &&& m_end.inner_perm.is_some()
    &&& m_end.inner_perm.unwrap()@.id() == self.inner_perm.unwrap()@.id()
    &&& m_end.inner_perm.unwrap()@.is_init()
    &&& m_end.inner_perm.unwrap()@.value() == inner
    &&& m_end.state ==self.state
    &&& m_end.usage == self.usage
    &&& m_end.ref_count == self.ref_count
    &&& m_end.address == self.address
    }
}

pub open spec fn seal_spec(&self) -> MetaSlotModel {
    MetaSlotModel {
        state: MetaSlotState::Used,
        ..*self
    }
}

pub open spec fn clear_inner_spec(&self, m_end: &MetaSlotModel) -> bool
{
    self.state == MetaSlotState::Used &&
    self.ref_count == 0 ==> {
    &&& m_end.ref_count_perm == self.ref_count_perm
    &&& m_end.inner_perm.is_some()
    &&& m_end.inner_perm.unwrap()@.id() == self.inner_perm.unwrap()@.id()
    &&& m_end.inner_perm.unwrap()@.is_uninit()
    &&& m_end.state == MetaSlotState::Finalizing
    &&& m_end.usage == self.usage
    &&& m_end.ref_count == self.ref_count
    &&& m_end.address == self.address
    }
}

pub open spec fn clear_spec(&self, m_end: &MetaSlotModel) -> bool
{
    self.state == MetaSlotState::Finalizing &&
    self.ref_count == 0 ==> {
    &&& m_end.ref_count_perm == self.ref_count_perm
    &&& m_end.inner_perm.is_none()
    &&& m_end.state == MetaSlotState::Unused
    &&& m_end.usage == PageUsage::Unused
    &&& m_end.ref_count == 0
    &&& m_end.address == self.address
    }
}
}
} // verus!
