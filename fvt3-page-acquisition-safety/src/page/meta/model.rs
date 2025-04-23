//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.

use vstd::prelude::*;
use vstd::cell::*;
use vstd::atomic::*;
use vstd::atomic_ghost::*;

use super::PageMeta;
use super::{PageUsage, MetaSlot, MetaSlotInner};
use crate::common::*;

verus! {

/// The actual usage of the MetaSlot.
///
/// It could be `Unused`, and at then contains Permission to write
/// to the `_inner` field.
///
/// When it turns into `Used`, it contains the actual usage of the page
/// and the Permission is transferred to the owner of the MetaSlot.
/// This realize the intention that we only allow the MetaSlot to be
/// typed once.
pub tracked enum ActualUsage {
    Unused(PointsTo<MetaSlotInner>),
    Used(PageUsage),
}
}

verus! {

/// Internal state of the MetaSlot.
#[derive(PartialEq)]
pub ghost enum MetaSlotState {
    Unused,
    Claimed,
    Used,
    Finalizing,
}
}

verus! {

/// The logical model of a metadata slot.
pub tracked struct MetaSlotModel {
    pub tracked ref_count_perm: Tracked<PermissionU32>,
    pub tracked inner_perm: Option<Tracked<PointsTo<MetaSlotInner>>>,
    pub ghost address: u64,
    pub ghost ref_count: u32,
    pub ghost state: MetaSlotState,
    pub ghost usage: PageUsage,
}

impl MetaSlotModel {

pub open spec fn invariants(&self) -> bool {
&&& self.ref_count_perm@.value() == self.ref_count@
&&& self.address < MAX_PADDR
&&& self.address % PAGE_SIZE == 0
&&& self.state == MetaSlotState::Unused ==> {
    &&& self.inner_perm.is_none()
    &&& self.ref_count == 0
    &&& self.usage == PageUsage::Unused
}
&&& self.state == MetaSlotState::Claimed ==> {
    &&& self.inner_perm.is_some()
    &&& self.usage != PageUsage::Unused
}
&&& self.state == MetaSlotState::Used ==> {
    &&& self.inner_perm.is_some()
    &&& self.inner_perm.unwrap()@.is_init()
    &&& self.usage != PageUsage::Unused
}
&&& self.state == MetaSlotState::Finalizing ==> {
    &&& self.inner_perm.is_some()
    &&& self.inner_perm.unwrap()@.is_uninit()
    &&& self.usage != PageUsage::Unused
}
}
}
}

verus! {
impl MetaSlot {

pub open spec fn id(&self) -> u64;

pub open spec fn invariant_id(&self) -> bool {
&&& self.id() % META_SLOT_SIZE == 0
&&& FRAME_METADATA_RANGE.start <= self.id()
&&& self.id() < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE as u64
}

pub open spec fn invariants(&self) -> bool {
&&& self.wf()
&&& self.invariant_id()
}

pub open spec fn relate_model(&self, model: &MetaSlotModel) -> bool
{
    self.invariants() ==> {
    &&& model.invariants()
    &&& model.address == meta_to_page(self.id())
    &&& self.ref_count.id() == model.ref_count_perm@.id()
    &&& model.state != MetaSlotState::Unused ==> {
        model.inner_perm.unwrap()@.id() == self._inner.id()
        }
    }
}

pub open spec fn inv_relate(&self, model: &MetaSlotModel) -> bool {
&&& self.invariants()
&&& self.relate_model(model)
}

pub proof fn invariants_implies_model(&self, model: &MetaSlotModel)
    requires
        self.invariants(),
        self.relate_model(model),
    ensures
        model.invariants()
{ }
}
}

verus! {

//
// # Primitives for MetaSlot
//
impl MetaSlot {

pub open spec fn model_from_paddr_spec(paddr: Paddr) -> Tracked<MetaSlotModel>;

pub open spec fn concrete_from_paddr_spec(paddr: Paddr) -> &'static Self;

#[verifier::external_body]
#[verifier::when_used_as_spec(concrete_from_paddr_spec)]
pub fn concrete_from_paddr(paddr: Paddr) -> (res: &'static Self)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        res == Self::concrete_from_paddr_spec(paddr),
        paddr == meta_to_page(res.id()),
{
    let vaddr = page_to_meta(paddr);
    let ptr = vaddr as *const MetaSlot;
    unsafe { &*ptr }
}

///
/// MetaSlot is statically bind to a physical address. In this case, we need to
/// provide the hypothesis that a concrete MetaSlot derived from `paddr` is
/// indeed attached to that physical address.
///
#[verifier::external_body]
pub proof fn axiom_concrete_from_paddr_id(paddr: Paddr)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR
    ensures
        paddr == meta_to_page(Self::concrete_from_paddr(paddr).id())
{ }

#[verifier::external_body]
#[verifier::when_used_as_spec(model_from_paddr_spec)]
pub fn model_from_paddr(paddr: Paddr) -> (res: Tracked<MetaSlotModel>)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        res == Self::model_from_paddr_spec(paddr),
        Self::concrete_from_paddr(paddr).invariants() ==> {
        &&& res@.invariants()
        &&& Self::concrete_from_paddr(paddr).relate_model(&res@)
        }
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn axiom_model_from_paddr_address(paddr: Paddr)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR
    ensures
        Self::model_from_paddr(paddr)@.address@ == paddr
{ }

#[verifier::external_body]
pub proof fn axiom_relate_model_same_paddr(paddr: Paddr,
    slot: &'static MetaSlot, model: &MetaSlotModel)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
        slot == MetaSlot::concrete_from_paddr(paddr),
        model == &MetaSlot::model_from_paddr(paddr)@,
        slot.invariants(),
    ensures
        slot.relate_model(model),
{ }

#[verifier::external_body]
pub proof fn axiom_meta_slot_model_singleton(a: &MetaSlotModel, b: &MetaSlotModel)
    requires
        a.address == b.address,
    ensures
        a == b,
{ }

pub fn from_paddr(paddr: Paddr)
    -> (res: (&'static Self, Tracked<MetaSlotModel>))
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        res.0 == MetaSlot::concrete_from_paddr(paddr),
        res.1 == MetaSlot::model_from_paddr(paddr),
        res.0.invariants() ==> {
        &&& res.1@.invariants()
        &&& res.0.inv_relate(&res.1@)
        }
{
    let slot: &'static MetaSlot = MetaSlot::concrete_from_paddr(paddr);
    let Tracked(model) = MetaSlot::model_from_paddr(paddr);
    (slot, Tracked(model))
}

#[verifier::external_body]
pub fn as_meta_slot_ptr(&self) -> (res: Vaddr)
    ensures
        res as int == self.id(),
{
    self as *const MetaSlot as Vaddr
}

}

}
