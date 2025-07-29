use vstd::prelude::*;
use vstd::simple_pptr::{self, *};
use vstd::cell;
use vstd::atomic::*;

use std::marker::PhantomData;
use std::ops::Range;

use crate::mm::*;

use crate::prelude::PageTablePageMetaInner;
use crate::prelude::PageUsage;

verus! {

pub mod kspace {
    use super::*;

    verus! {
    pub const FRAME_METADATA_RANGE: Range<usize> = 0xffff_e000_0000_0000..0xffff_e100_0000_0000;
    }
}

pub mod frame {
    use super::*;

    verus! {
    pub const MAX_PADDR: usize = 0x1_0000;
    }
}


pub mod mapping {
    use vstd::prelude::*;
    use super::kspace::*;
    use super::frame::*;

    verus! {

    pub open spec fn frame_to_meta_spec(paddr: usize) -> (res: usize)
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR,
    {
        let base = FRAME_METADATA_RANGE.start;
        let offset = paddr / 4096;
        (base + offset * super::meta_slot_size()) as usize
    }

    #[verifier::allow_in_spec]
    pub const fn frame_to_meta(paddr: usize) -> (res: usize)
        requires
            paddr % 4096 == 0,
            paddr < MAX_PADDR,
        returns
            frame_to_meta_spec(paddr)
    {
        let base = FRAME_METADATA_RANGE.start;
        let offset = paddr / 4096;
        base + offset * super::meta_slot_size()
    }

    pub open spec fn max_meta_slots() -> int {
        (FRAME_METADATA_RANGE.end - FRAME_METADATA_RANGE.start) / super::meta_slot_size() as int
    }

    pub open spec fn meta_addr(i: usize) -> (res: usize)
        recommends
            0 <= i < max_meta_slots() as usize,
    {
        (FRAME_METADATA_RANGE.start + i * super::meta_slot_size()) as usize
    }

    pub open spec fn meta_to_frame_spec(vaddr: usize) -> usize
        recommends
            vaddr % size_of::<super::MetaSlot>() == 0,
            FRAME_METADATA_RANGE.start <= vaddr < FRAME_METADATA_RANGE.end,
    {
        let offset = (vaddr - FRAME_METADATA_RANGE.start) / size_of::<super::MetaSlot>() as int;
        (offset * 4096) as usize
    }

    }
}

pub trait Inv {
    spec fn inv(&self) -> bool;
}

pub trait InvView: Inv {
    type V: Inv;

    spec fn view(&self) -> Self::V
        recommends self.inv();

    proof fn view_preserves_inv(&self)
        requires self.inv(),
        ensures self.view().inv(),
    ;
}


pub trait OwnerOf {
    /// The owner of the concrete type.
    /// The Owner must implement `Inv`, indicating that it must
    /// has a consistent state.
    type Owner: InvView;

    spec fn wf(&self, owner: &Self::Owner) -> bool
        recommends owner.inv(),
    ;
}

pub trait ModelOf: OwnerOf {
    open spec fn model(&self, owner: &Self::Owner) -> <Self::Owner as InvView>::V
        recommends
            self.wf(owner),
    {
        owner.view()
    }
}

 

pub const REF_COUNT_UNUSED: u64 = u64::MAX;
pub const REF_COUNT_UNIQUE: u64 = u64::MAX - 1;
pub const REF_COUNT_MAX: u64 = i64::MAX as u64;

#[rustc_has_incoherent_inherent_impls]
pub struct Link {
    pub next: Option<PPtr<Link>>,
    pub prev: Option<PPtr<Link>>,
}

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    FrameLink(Link),
    PTNode(PageTablePageMetaInner),
}

/// Concrete type
#[rustc_has_incoherent_inherent_impls]
pub struct MetaSlot {
    pub storage: cell::PCell<MetaSlotStorage>,
    pub ref_count: PAtomicU64,
    pub vtable_ptr: PPtr<usize>,
    pub in_list: PAtomicU64,
}

global layout MetaSlot is size == 64, align == 8;

pub proof fn size_of_meta_slot()
    ensures
        size_of::<MetaSlot>() == 64,
        align_of::<MetaSlot>() == 8,
{ }

#[inline(always)]
#[verifier::allow_in_spec]
pub const fn meta_slot_size() -> (res: usize)
    returns 64usize
{
    size_of::<MetaSlot>()
}


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


pub enum MetaSlotStatus {
    UNUSED,
    UNIQUE,
    SHARED,
    OVERFLOW,
    UNDER_CONSTRUCTION,
}


pub ghost struct MetaSlotModel {
    pub status: MetaSlotStatus,
    pub storage: MemContents<MetaSlotStorage>,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
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





/// Represents the meta-frame memory region. Can be viewed as a collection of
/// Cell<MetaSlot> at a fixed address range.
pub struct MetaRegion;

pub tracked struct MetaRegionOwners {
    pub slots: Map<usize, Tracked<simple_pptr::PointsTo<MetaSlot>>>,
    pub slot_owners: Map<usize, MetaSlotOwner>,
}

pub ghost struct MetaRegionModel {
    pub slots: Map<usize, MetaSlotModel>,
}

impl Inv for MetaRegionOwners {
    open spec fn inv(&self) -> bool {
    &&& self.slots.dom().finite()
    &&& self.slots.dom() == self.slot_owners.dom()
    &&& {
        // All accessible slots are within the valid address range.
        forall |i: usize|
            i < mapping::max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        }
    &&& {
        // Invariant for each slot holds.
        forall |i: usize|
            #[trigger]
            self.slots.contains_key(i) ==>
            {
            &&& self.slot_owners.contains_key(i)
            &&& self.slot_owners[i].inv()
            &&& self.slots[i]@.is_init()
            &&& self.slots[i]@.addr() == mapping::meta_addr(i)
            &&& self.slots[i]@.value().wf(&self.slot_owners[i])
            &&& self.slot_owners[i].self_ptr@.addr() == self.slots[i]@.addr()
            }
    }
    }
}

impl Inv for MetaRegionModel {
    open spec fn inv(&self) -> bool {
    &&& self.slots.dom().finite()
    &&& forall |i: usize| i < mapping::max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
    &&& forall |i: usize| #[trigger] self.slots.contains_key(i) ==> self.slots[i].inv()
    }
}


impl InvView for MetaRegionOwners {
    type V = MetaRegionModel;

    open spec fn view(&self) -> Self::V {
        let slots = self.slot_owners.map_values(
            |s: MetaSlotOwner|
            s.view()
        );
        MetaRegionModel {
            slots,
        }
    }

    // XXX: verus `map_values` does not preserves the `finite()` attribute.
    axiom fn view_preserves_inv(&self);
}

impl OwnerOf for MetaRegion {
    type Owner = MetaRegionOwners;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        true
    }
}

impl ModelOf for MetaRegion { }

impl MetaRegionOwners {
    pub open spec fn ref_count(self, i: usize) -> (res: u64)
        recommends
            self.inv(),
            i < mapping::max_meta_slots() as usize,
    {
        self.slot_owners[i].ref_count@.value()
    }
}


pub open spec fn get_slot_spec(paddr: Paddr) -> (res: PPtr<MetaSlot>)
    recommends
        paddr % 4096 == 0,
        paddr < frame::MAX_PADDR,
{
    let slot = mapping::frame_to_meta(paddr);
    PPtr(slot, PhantomData::<MetaSlot>)
}


/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta {
    exec fn on_drop(&mut self) {}

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;

    spec fn cast_to(x: &MetaSlotStorage) -> &Self;

    spec fn write_as(&self) -> MetaSlotStorage;
}


impl MetaSlot {

    pub open spec fn get_from_unused_spec<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionModel,
    ) -> (PPtr<MetaSlot>, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let ptr = get_slot_spec(paddr);
        let idx = paddr / 4096;
        let (rc, status) = if as_unique_ptr {
            (REF_COUNT_UNIQUE, MetaSlotStatus::UNIQUE)
        } else {
            (1, MetaSlotStatus::SHARED)
        };
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx, MetaSlotModel {
                    status,
                    storage: MemContents::Init(metadata.write_as()),
                    ref_count: rc,
                    vtable_ptr: MemContents::Init(metadata.vtable_ptr()),
                    in_list: 0,
                    self_addr: ptr.addr(),
                    usage: PageUsage::Frame,
                }
            )
        };
        (ptr, post)
    }

    /// All other slots remain unchanged.
    pub open spec fn update_index_tracked(idx: usize, pre: MetaRegionOwners, post: MetaRegionOwners)
        -> bool
        recommends
            pre.slots.contains_key(idx)
    {
    &&& pre.slots.dom() == post.slots.dom()
    &&& pre.slot_owners.dom() == post.slot_owners.dom()
    &&& forall |i: usize| #[trigger]
        pre.slots.contains_key(i) && i != idx ==>
            pre.slots[i] == post.slots[i]
    &&& forall |i: usize| #[trigger]
        pre.slot_owners.contains_key(i) && i != idx ==>
            pre.slot_owners[i] == post.slot_owners[i]
    }


    pub open spec fn get_from_unused_tracked<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.view().slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let idx = paddr / 4096;
        {
        &&& Self::update_index_tracked(idx, pre, post)
        &&& Self::get_from_unused_spec(paddr, metadata, as_unique_ptr, pre.view()).1 ==
            post.view()
        }
    }

    pub open spec fn get_from_in_use_spec(paddr: Paddr, pre: MetaRegionModel) 
        -> (PPtr<MetaSlot>, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            0 <= pre.slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let ptr = get_slot_spec(paddr);
        let idx = paddr / 4096;
        let pre_slot = pre.slots[idx];
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx, MetaSlotModel {
                    ref_count: (pre_slot.ref_count + 1) as u64,
                    ..pre_slot
                }
            )
        };
        (ptr, post)
    }

    pub open spec fn get_from_in_use_tracked(
        paddr: Paddr,
        // -- ghost parameters --
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            0 <= pre.view().slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let idx = paddr / 4096;
        {
        &&& Self::update_index_tracked(idx, pre, post)
        &&& Self::get_from_in_use_spec(paddr, pre.view()).1 == post.view()
        }
    }

    pub open spec fn inc_ref_count_spec(&self, pre: MetaSlotModel)
        -> (MetaSlotModel)
        recommends
            pre.inv(),
            pre.status == MetaSlotStatus::SHARED,
    {
        MetaSlotModel {
            ref_count: (pre.ref_count + 1) as u64,
            ..pre
        }
    }

    pub open spec fn frame_paddr(&self, pre: MetaSlotModel) -> Paddr {
        mapping::meta_to_frame_spec(pre.self_addr)
    }
}


pub struct UniqueFrame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

pub tracked struct UniqueFrameOwner {
    pub slot: Tracked<MetaSlotOwner>,
}

pub ghost struct UniqueFrameModel {
    pub slot: MetaSlotModel,
}


impl Inv for UniqueFrameOwner {
    open spec fn inv(&self) -> bool {
    &&& self.slot@.inv()
    &&& self.slot@.ref_count@.value() == REF_COUNT_UNIQUE
    &&& self.slot@.vtable_ptr@.is_init()
    &&& self.slot@.storage@.is_init()
    }
}

impl Inv for UniqueFrameModel {
    open spec fn inv(&self) -> bool {
    &&& self.slot.inv()
    &&& self.slot.status == MetaSlotStatus::UNIQUE
    &&& self.slot.ref_count == REF_COUNT_UNIQUE
    &&& self.slot.vtable_ptr.is_init()
    &&& self.slot.storage.is_init()
    }
}

impl InvView for UniqueFrameOwner {
    type V = UniqueFrameModel;

    open spec fn view(&self) -> Self::V {
        UniqueFrameModel {
            slot: self.slot@.view(),
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl <M: AnyFrameMeta> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
    &&& self.ptr == owner.slot@.self_ptr@.pptr()
    }
}

impl <M: AnyFrameMeta> ModelOf for UniqueFrame<M> { }

impl <M: AnyFrameMeta> UniqueFrame<M> {

    pub open spec fn from_unused_spec(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        -> (Self, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let (ptr, post) = MetaSlot::get_from_unused_spec(paddr, metadata, true, pre);
        (UniqueFrame { ptr, _marker: PhantomData }, post)
    }


    pub proof fn from_unused_properties(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        requires
            paddr % 4096 == 0,
            paddr < frame::MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
        ensures
            UniqueFrame::from_unused_spec(paddr, metadata, pre).1.inv(),
    { }

    pub open spec fn meta_spec(&self, pre: UniqueFrameModel) -> &M 
        recommends
            pre.inv(),
    {
        M::cast_to(&pre.slot.storage.value())
    }

    pub open spec fn replace_spec(&self, metadata: M, pre: UniqueFrameModel)
        -> UniqueFrameModel
        recommends
            pre.inv(),
    {
        let storage = MemContents::Init(metadata.write_as());
        UniqueFrameModel {
            slot: MetaSlotModel {
                storage,
                ..pre.slot
            }
        }
    }

}



}

