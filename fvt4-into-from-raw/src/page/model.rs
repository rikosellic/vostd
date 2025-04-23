use vstd::prelude::*;
use vstd::simple_pptr;

use super::*;
use super::AbstractState;
use super::meta::model::*;
use crate::common::*;

verus! {

pub enum PageState {
    Unused,
    Typed,
    Untyped,
}

pub enum PageOwner {
    Kernel { context_id: int },
    User { thread_id: int },
    Dma,
    Cpu,
    PageTable,
}

pub enum PageUsePermission {
    NoPerm,
    RawPointer,
    PageTableEntry,
    ReadWrite,
}
}

verus! {

impl PageUsage {

pub open spec fn as_state_spec(&self) -> (res: PageState) {
    match &self {
        PageUsage::Unused => PageState::Unused,
        PageUsage::Frame => PageState::Untyped,
        _ => PageState::Typed,
    }
}

#[verifier::when_used_as_spec(as_state_spec)]
pub fn as_state(&self) -> (res: PageState)
    ensures
        res == self.as_state_spec()
{
    match &self {
        PageUsage::Unused => PageState::Unused,
        PageUsage::Frame => PageState::Untyped,
        _ => PageState::Typed,
    }
}

pub open spec fn as_numeric_spec(&self) -> (res: u8) {
    match &self {
        PageUsage::Unused => 0,
        PageUsage::Reserved => 1,
        PageUsage::Frame => 32,
        PageUsage::PageTable => 64,
        PageUsage::Meta => 65,
        PageUsage::Kernel => 66,
    }
}

#[verifier::when_used_as_spec(as_numeric_spec)]
pub fn as_numeric(&self) -> (res: u8)
    ensures
        res == self.as_numeric_spec()
{
    match &self {
        PageUsage::Unused => 0,
        PageUsage::Reserved => 1,
        PageUsage::Frame => 32,
        PageUsage::PageTable => 64,
        PageUsage::Meta => 65,
        PageUsage::Kernel => 66,
    }
}
}
} // verus!

verus! {
pub tracked struct PageModel {
    pub index: u64,
    pub ghost state: PageState,
    pub ghost usage: PageUsage,
    pub ghost ref_count: int,
    pub ghost owners: Set<PageOwner>,
    pub tracked ptr_perm: Tracked<simple_pptr::PointsTo<MetaSlot>>,
}
}

verus! {

impl PageModel {
    pub open spec fn field_invariants(&self) -> bool {
        &&& 0 <= self.index && self.index < MAX_PADDR / PAGE_SIZE
        &&& self.owners.finite()
        &&& FRAME_METADATA_RANGE.start + self.index * META_SLOT_SIZE == self.ptr_perm@.addr()
    }

    pub open spec fn state_invariants(&self) -> bool {
        match self.state {
            PageState::Unused => {
                &&& self.usage == PageUsage::Unused
                &&& self.ref_count == 0
                &&& self.owners.is_empty()
            },
            PageState::Typed => {
                &&& self.usage.as_state() == self.state
                &&& self.ref_count > 0
                &&& !self.owners.is_empty()
                &&& self.ref_count >= self.owners.len() as int
            },
            PageState::Untyped => {
                &&& self.usage.as_state() == self.state
                &&& self.ref_count > 0
                &&& !self.owners.is_empty()
                &&& self.ref_count >= self.owners.len() as int
            },
        }
    }

    pub open spec fn invariants(&self) -> bool {
        &&& self.field_invariants()
        &&& self.state_invariants()
    }

    pub open spec fn step_invariants(&self, next: &Self) -> bool {
        &&& next.index == self.index
    }

    pub open spec fn relate_paddr(&self, paddr: Paddr) -> bool {
    &&& paddr == self.index * PAGE_SIZE
    }

    #[verifier::external_body]
    pub proof fn axiom_page_model_singleton(a: &PageModel, b: &PageModel, paddr: Paddr)
        requires
            a.relate_paddr(paddr),
            b.relate_paddr(paddr),
        ensures
            a == b,
    {
        assert(a.index == b.index);
    }

    pub open spec fn relate_page<M: PageMeta>(&self, page: &Page<M>) -> bool {
    &&& FRAME_METADATA_RANGE.start + self.index * META_SLOT_SIZE == page.ptr.addr()
    }

    pub open spec fn relate_meta_slot(&self, slot: &MetaSlot) -> bool {
    &&& FRAME_METADATA_RANGE.start + self.index * META_SLOT_SIZE == slot.id()
    }

    pub open spec fn relate_meta_slot_model(&self, slot: &MetaSlotModel) -> bool {
    &&& self.index * PAGE_SIZE == slot.address@
    }

    pub open spec fn relate_meta_slot_model_properties(&self, slot: &MetaSlotModel) -> bool {
    &&& match (self.state, slot.state, slot.usage) {
        (PageState::Unused,  MetaSlotState::Unused, PageUsage::Unused) => true,
        (PageState::Untyped, MetaSlotState::Used,   PageUsage::Frame) => true,
        (PageState::Typed,   MetaSlotState::Used, _) => true,
        _ => false,
        }
    &&& self.usage == slot.usage
    &&& self.ref_count == slot.ref_count
    &&& self.ptr_perm@.addr() == page_to_meta(slot.address)
    }

    pub open spec fn relate_meta_slot_full(&self, slot: &MetaSlotModel) -> bool {
    &&& self.relate_meta_slot_model(slot)
    &&& self.relate_meta_slot_model_properties(slot)
    }

    #[verifier::external_body]
    pub proof fn axiom_relate_meta_slot_model_properties(&self, slot: &MetaSlotModel)
        requires
            slot.invariants(),
            self.relate_meta_slot_model(slot),
        ensures
            self.relate_meta_slot_model_properties(slot),
    { }
}
} // verus!

verus! {

impl<M: PageMeta> Page<M> {

pub open spec fn relate_model(&self, model: &PageModel) -> bool {
&&& self.ptr.addr() == FRAME_METADATA_RANGE.start + model.index * META_SLOT_SIZE
}

pub open spec fn relate_meta_slot(&self, slot: &MetaSlot) -> bool {
    self.ptr.addr() == slot.id()
}

pub proof fn lemma_relate_same_meta_slot_relate_model(&self, model: &PageModel,
    slot: &MetaSlot)
    requires
        self.relate_meta_slot(slot),
        model.relate_meta_slot(slot),
    ensures
        self.relate_model(model),
{}
}
}

verus! {

impl<M: PageMeta> Page<M> {

pub open spec fn from_slot_spec(slot: &MetaSlot) -> Page<M>;

#[verifier::external_body]
#[verifier::when_used_as_spec(from_slot_spec)]
pub fn from_slot(slot: &MetaSlot) -> (res: Page<M>)
    ensures
        res == Self::from_slot_spec(slot),
        slot.id() == res.ptr.addr(),
{
    let addr: usize = slot as *const MetaSlot as usize;
    let ptr = PPtr::from_usize(addr);
    Page {
        ptr,
        _marker: PhantomData,
    }
}

#[verifier::external_body]
pub proof fn from_slot_spec_ensures(slot: &MetaSlot)
    ensures
        Self::from_slot(slot).relate_meta_slot(slot),
{ }

pub open spec fn model_from_slot_spec(slot: &MetaSlot) -> Tracked<PageModel>;

#[verifier::external_body]
#[verifier::when_used_as_spec(model_from_slot_spec)]
pub fn model_from_slot(slot: &MetaSlot) -> (res: Tracked<PageModel>)
    ensures
        res == Self::model_from_slot_spec(slot),
        slot.id() == res@.index * META_SLOT_SIZE,
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn model_from_slot_spec_ensures(slot: &MetaSlot)
    ensures
        Self::model_from_slot(slot)@.relate_meta_slot(slot),
{ }

pub proof fn model_from_slot_relate_abstract_data(paddr: Paddr, slot: &MetaSlot,
    model: &PageModel, s: &AbstractState)
    requires
        s.invariants(),
        paddr < MAX_PADDR,
        paddr % PAGE_SIZE == 0,
        slot == MetaSlot::concrete_from_paddr(paddr),
        model == Page::<M>::model_from_slot(slot)@,
    ensures
        s.get_page(paddr) == model,
{
    let x = s.get_page(paddr);
    assert(x.relate_paddr(paddr)) by {
        s.get_page_relate_to_paddr(paddr);
    };
    assert(paddr == meta_to_page(slot.id())) by {
        MetaSlot::axiom_concrete_from_paddr_id(paddr);
    };
    assert(model.relate_meta_slot(slot)) by {
        Page::<M>::model_from_slot_spec_ensures(slot);
    };
    assert(FRAME_METADATA_RANGE.start + model.index * META_SLOT_SIZE == slot.id());
    assert(model.relate_paddr(paddr));
    assert(x == model) by {
        PageModel::axiom_page_model_singleton(x, model, paddr);
    };
}

pub open spec fn new_spec(slot: &MetaSlot) -> (res: (Page<M>, Tracked<PageModel>))
{
    let page = Page::from_slot(slot);
    let model = Page::<M>::model_from_slot(slot);
    (page, model)
}

pub proof fn new_spec_ensures(slot: &MetaSlot)
    ensures
        Self::new(slot).0.relate_meta_slot(slot),
        Self::new(slot).1@.relate_meta_slot(slot),
{
    let (page, model) = Self::new(slot);
    Self::from_slot_spec_ensures(slot);
    Self::model_from_slot_spec_ensures(slot);
}

#[verifier::when_used_as_spec(new_spec)]
pub fn new(slot: &MetaSlot) -> (res: (Page<M>, Tracked<PageModel>))
    ensures
        res == Self::new_spec(slot),
        res.0 == Self::from_slot(slot),
        res.1 == Self::model_from_slot(slot),
        res.0.relate_meta_slot(slot),
        res.1@.relate_meta_slot(slot),
        res.0.relate_model(&res.1@),
{
    let page = Page::from_slot(slot);
    let Tracked(model) = Page::<M>::model_from_slot(slot);
    proof {
        Self::new_spec_ensures(slot);
    }
    (page, Tracked(model))
}

} // impl<M: PageMeta> Page<M>

} // verus!
