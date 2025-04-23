pub mod meta;
pub mod model;
pub mod proofs;
pub mod specs;

use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

use std::marker::PhantomData;
use std::{ops::Range, sync::atomic::*, mem::size_of};
use crate::common::*;
use crate::abstract_state::{AbstractState, panic};

use meta::*;
use meta::model::{MetaSlotState, MetaSlotModel};
use specs::*;
use model::*;

verus! {

/// A page with a statically-known usage, whose metadata is represented by `M`.
pub struct Page<M: PageMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

} // verus!
verus! {

impl<M: PageMeta> Page<M> {
    pub fn from_unused(paddr: Paddr, Tracked(s): Tracked<AbstractState>) -> (res: (
        Option<Self>,
        Tracked<AbstractState>,
    ))
        requires
            s.invariants(),
            0 <= paddr && paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
            MetaSlot::concrete_from_paddr(paddr).invariants(),
            s.get_page(paddr).state == PageState::Unused,
            s.get_page(paddr).ref_count == 0,
            s.get_page(paddr).relate_meta_slot_full(&s.get_meta_slot(paddr)),
        ensures
            PageModel::from_unused_spec(paddr, res.0, s, res.1@),
            res.1@.get_page(paddr).relate_meta_slot_full(&res.1@.get_meta_slot(paddr)),
    {
        let (slot, Tracked(slot_model)) = MetaSlot::from_paddr(paddr);
        assert(slot.inv_relate(&slot_model));
        assert(slot_model == s.get_meta_slot(paddr)) by {
            assert(s.get_meta_slot(paddr).address == paddr) by {
                s.get_meta_slot_relate_to_paddr(paddr);
            };
            assert(slot_model.address == paddr) by {
                assert(slot_model == MetaSlot::model_from_paddr_spec(paddr));
                MetaSlot::axiom_model_from_paddr_address(paddr);
            };
            MetaSlot::axiom_meta_slot_model_singleton(&slot_model, &s.get_meta_slot(paddr));
        };

        let (page, Tracked(page_model)) = Page::<M>::new(slot);
        assert(page_model.relate_meta_slot(&slot));
        assert(page_model.relate_meta_slot_model(&slot_model));
        assert(page_model == s.get_page(paddr)) by {
            Page::<M>::model_from_slot_relate_abstract_data(paddr, &slot, &page_model, &s);
        };
        assert(page_model.relate_meta_slot_full(&slot_model));
        assert(page_model.state == PageState::Unused);
        assert(slot_model.state == MetaSlotState::Unused);
        assert(slot_model.usage == PageUsage::Unused);
        assert(page_model.ref_count == 0);
        assert(slot_model.ref_count == 0);

        let usage = M::get_usage();
        assert(usage != PageUsage::Unused);

        let (rv, Tracked(slot_model_claimed)) = slot.claim(usage, Tracked(slot_model));
        if !rv {
            assert(slot_model_claimed == slot_model);
            assert(page_model.relate_meta_slot_full(&slot_model_claimed));

            let Tracked(s_panic) = panic(Tracked(s), "Failed to claim slot");
            let tracked s_end = AbstractState {
                meta_slots: s.meta_slots.insert(
                    paddr as int / PAGE_SIZE as int,
                    slot_model_claimed,
                ),
                ..s_panic
            };

            let r = (None, Tracked(s_end));
            assert(PageModel::from_unused_spec_failure(paddr, r.0, s, r.1@));
            return r;
        }
        assert(rv == true);
        assert(slot_model_claimed.state == MetaSlotState::Claimed);
        assert(slot_model_claimed.usage == usage);
        assert(slot_model_claimed.inner_perm.is_some());
        assert(slot_model_claimed.inner_perm.unwrap()@.is_uninit());
        assert(slot_model_claimed.ref_count == 0);

        let (_, Tracked(slot_model_claimed)) = slot.inc0(Tracked(slot_model_claimed));

        assert(slot_model_claimed.state == MetaSlotState::Claimed);
        assert(slot_model_claimed.inner_perm.unwrap()@.is_uninit());

        let inner = MetaSlotInner::new::<M>();
        let Tracked(slot_model_claimed) = slot.put_inner(inner, Tracked(slot_model_claimed));
        let Tracked(slot_model_sealed) = slot.seal(Tracked(slot_model_claimed));

        let tracked page_model = PageModel {
            state: usage.as_state(),
            usage,
            ref_count: 1,
            owners: Set::empty().insert(PageOwner::Kernel { context_id: s.context_id }),
            ..page_model
        };
        assert(page_model.invariants());

        let tracked s_end = AbstractState {
            meta_slots: s.meta_slots.insert(paddr as int / PAGE_SIZE as int, slot_model_sealed),
            pages: s.pages.insert(paddr as int / PAGE_SIZE as int, page_model),
            ..s
        };
        assert(s_end.get_page(paddr) == &page_model);
        assert(s_end.get_meta_slot(paddr) == &slot_model_sealed);

        assert(page_model.relate_meta_slot_full(&slot_model_sealed));
        let r = (Some(page), Tracked(s_end));
        assert(PageModel::from_unused_spec_success(paddr, r.0, s, r.1@));
        r
    }
}

} // verus!
