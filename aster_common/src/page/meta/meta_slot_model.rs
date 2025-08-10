//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::prelude::*;
use vstd::cell;
use vstd::simple_pptr::{self, PPtr};
use vstd::atomic::*;

use vstd_extra::ownership::*;

use crate::prelude::*;

verus! {

pub enum MetaSlotStatus {
    UNUSED,
    UNIQUE,
    SHARED,
    OVERFLOW,
    UNDER_CONSTRUCTION,
}

/* Phase I version; TODO: check conversions
#[derive(PartialEq)]
pub ghost enum MetaSlotState {
    Unused,
    Claimed,
    Used,
    Finalizing,
} */

pub const REF_COUNT_UNUSED: u64 = u64::MAX;
pub const REF_COUNT_UNIQUE: u64 = u64::MAX - 1;
pub const REF_COUNT_MAX: u64 = i64::MAX as u64;


} // verus!

verus! {

pub tracked struct MetaSlotOwner {
    pub storage: Tracked<cell::PointsTo<MetaSlotStorage>>,
    pub ref_count: Tracked<PermissionU64>,
    pub vtable_ptr: Tracked<simple_pptr::PointsTo<usize>>,
    pub in_list: Tracked<PermissionU64>,
    pub self_ptr: Tracked<simple_pptr::PointsTo<MetaSlot>>,
    pub usage: PageUsage,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(&self) -> bool {
    &&& self.ref_count@.value() == REF_COUNT_UNUSED ==> {
        &&& self.vtable_ptr@.is_uninit()
        &&& self.in_list@.value() == 0
        }
    &&& self.ref_count@.value() == REF_COUNT_UNIQUE ==> {
        &&& self.vtable_ptr@.is_init()
        }
    &&& 0 < self.ref_count@.value() < REF_COUNT_MAX ==> {
        &&& self.vtable_ptr@.is_init()
        }
    &&& REF_COUNT_MAX <= self.ref_count@.value() < REF_COUNT_UNUSED ==> {
        false
        }
    &&& self.ref_count@.value() == 0 ==> {
        &&& self.vtable_ptr@.is_uninit()
        &&& self.in_list@.value() == 0
        }
    }
}

pub ghost struct MetaSlotModel {
    pub status: MetaSlotStatus,
    pub storage: cell::MemContents<MetaSlotStorage>,
    pub ref_count: u64,
    pub vtable_ptr: simple_pptr::MemContents<usize>,
    pub in_list: u64,
    pub self_addr: usize,
    pub usage: PageUsage,
}

impl Inv for MetaSlotModel {
    open spec fn inv(&self) -> bool {
    match self.ref_count {
        REF_COUNT_UNUSED => {
        &&& self.vtable_ptr.is_uninit()
        &&& self.in_list == 0
        },
        REF_COUNT_UNIQUE => {
        &&& self.vtable_ptr.is_init()
        },
        0 => {
        &&& self.vtable_ptr.is_uninit()
        &&& self.in_list == 0
        },
        _ if self.ref_count < REF_COUNT_MAX => {
        &&& self.vtable_ptr.is_init()
        },
        _ => {
        false
        },
    }
    }
}

/* Phase 1 version; TODO: check that we don't need any of it!

impl MetaSlotModel {
    pub open spec fn invariants(&self) -> bool {
        &&& self.ref_count_perm@.value() == self.ref_count@
        &&& self.address < MAX_PADDR()
        &&& self.address % PAGE_SIZE() as u64 == 0
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
}*/

impl InvView for MetaSlotOwner {
    type V = MetaSlotModel;

    open spec fn view(&self) -> Self::V {
        let storage = self.storage@.mem_contents();
        let ref_count = self.ref_count@.value();
        let vtable_ptr = self.vtable_ptr@.mem_contents();
        let in_list = self.in_list@.value();
        let self_addr = self.self_ptr@.addr();
        let usage = self.usage;
        let status = match ref_count {
            REF_COUNT_UNUSED => MetaSlotStatus::UNUSED,
            REF_COUNT_UNIQUE => MetaSlotStatus::UNIQUE,
            0 => MetaSlotStatus::UNDER_CONSTRUCTION,
            _ if ref_count < REF_COUNT_MAX => MetaSlotStatus::SHARED,
            _ => MetaSlotStatus::OVERFLOW,
        };
        MetaSlotModel {
            status,
            storage,
            ref_count,
            vtable_ptr,
            in_list,
            self_addr,
            usage,
        }
    }

    proof fn view_preserves_inv(&self) { admit() }
}

impl OwnerOf for MetaSlot {
    type Owner = MetaSlotOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
    &&& self.storage.id() == owner.storage@.id()
    &&& self.ref_count.id() == owner.ref_count@.id()
    &&& self.vtable_ptr == owner.vtable_ptr@.pptr()
    &&& self.in_list.id() == owner.in_list@.id()
    }
}

impl ModelOf for MetaSlot { }

} // verus!
/*verus! {

impl MetaSlot {
    #[rustc_allow_incoherent_impl]
    pub open spec fn id(&self) -> u64;

    #[rustc_allow_incoherent_impl]
    pub open spec fn invariant_id(&self) -> bool {
        &&& self.id() % META_SLOT_SIZE() as u64 == 0
        &&& FRAME_METADATA_RANGE().start <= self.id()
        &&& self.id() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE() as u64
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn invariants(&self) -> bool {
        &&& self.wf()
        &&& self.invariant_id()
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_model(&self, model: &MetaSlotModel) -> bool {
        self.invariants() ==> {
            &&& model.invariants()
            &&& model.address == meta_to_page(self.id() as usize)
            &&& self.ref_count.id() == model.ref_count_perm@.id()
            &&& model.state != MetaSlotState::Unused ==> {
                model.inner_perm.unwrap()@.id() == self._inner.id()
            }
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inv_relate(&self, model: &MetaSlotModel) -> bool {
        &&& self.invariants()
        &&& self.relate_model(model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn invariants_implies_model(&self, model: &MetaSlotModel)
        requires
            self.invariants(),
            self.relate_model(model),
        ensures
            model.invariants(),
    {
    }
}

} // verus!
verus! {

//
// # Primitives for MetaSlot
//
impl MetaSlot {
    #[rustc_allow_incoherent_impl]
    pub open spec fn model_from_paddr_spec(paddr: Paddr) -> Tracked<MetaSlotModel>;

    #[rustc_allow_incoherent_impl]
    pub open spec fn concrete_from_paddr_spec(paddr: Paddr) -> &'static Self;

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(concrete_from_paddr_spec)]
    pub fn concrete_from_paddr(paddr: Paddr) -> (res: &'static Self)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            res == Self::concrete_from_paddr_spec(paddr),
            paddr == meta_to_page(res.id() as usize),
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
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_concrete_from_paddr_id(paddr: Paddr)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            paddr == meta_to_page(Self::concrete_from_paddr(paddr).id() as usize),
    {
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(model_from_paddr_spec)]
    pub fn model_from_paddr(paddr: Paddr) -> (res: Tracked<MetaSlotModel>)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            res == Self::model_from_paddr_spec(paddr),
            Self::concrete_from_paddr(paddr).invariants() ==> {
                &&& res@.invariants()
                &&& Self::concrete_from_paddr(paddr).relate_model(&res@)
            },
    {
        unimplemented!()
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_model_from_paddr_address(paddr: Paddr)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            Self::model_from_paddr(paddr)@.address@ == paddr,
    {
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_relate_model_same_paddr(
        paddr: Paddr,
        slot: &'static MetaSlot,
        model: &MetaSlotModel,
    )
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
            slot == MetaSlot::concrete_from_paddr(paddr),
            model == &MetaSlot::model_from_paddr(paddr)@,
            slot.invariants(),
        ensures
            slot.relate_model(model),
    {
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_meta_slot_model_singleton(a: &MetaSlotModel, b: &MetaSlotModel)
        requires
            a.address == b.address,
        ensures
            a == b,
    {
    }

    #[rustc_allow_incoherent_impl]
    pub fn from_paddr(paddr: Paddr) -> (res: (&'static Self, Tracked<MetaSlotModel>))
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            res.0 == MetaSlot::concrete_from_paddr(paddr),
            res.1 == MetaSlot::model_from_paddr(paddr),
            res.0.invariants() ==> {
                &&& res.1@.invariants()
                &&& res.0.inv_relate(&res.1@)
            },
    {
        let slot: &'static MetaSlot = MetaSlot::concrete_from_paddr(paddr);
        let Tracked(model) = MetaSlot::model_from_paddr(paddr);
        (slot, Tracked(model))
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn as_meta_slot_ptr(&self) -> (res: Vaddr)
        ensures
            res as int == self.id(),
    {
        self as *const MetaSlot as Vaddr
    }
}

} // verus!
*/