pub mod meta;
pub mod model;
pub mod proofs;
pub mod specs;

use vstd::prelude::*;
use vstd::simple_pptr::*;

use std::marker::PhantomData;
use std::{ops::Range, sync::atomic::*};
use crate::common::*;
use crate::abstract_state::{AbstractState, panic};
use crate::rust_core_mem::*;

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
    global layout usize is size == 8;

use core::mem::size_of;

impl<M: PageMeta> Page<M> {

    pub fn from_unused(paddr: Paddr, Tracked(s): Tracked<AbstractState>)
        -> (res: (Option<Self>, Tracked<AbstractState>))
        requires
            s.invariants(),
            0 <= paddr && paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
            MetaSlot::concrete_from_paddr(paddr).invariants(),
            s.get_page(paddr).state == PageState::Unused,
            s.get_page(paddr).ref_count == 0,
            s.get_page(paddr).relate_meta_slot_full(&s.get_meta_slot(paddr)),
        ensures
            PageModel::from_unused_spec(paddr, res.0, &s, &res.1@),
            res.1@.get_page(paddr).relate_meta_slot_full(&
                res.1@.get_meta_slot(paddr)),
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
                meta_slots: s.meta_slots.insert(paddr as int / PAGE_SIZE as int, slot_model_claimed),
                ..s_panic
            };

            let r = (None, Tracked(s_end));
            assert(PageModel::from_unused_spec_failure(paddr, r.0, &s, &r.1@));
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
            owners: Set::empty().insert(PageOwner::Kernel{context_id: s.context_id}),
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
        assert(PageModel::from_unused_spec_success(paddr, r.0, &s, &r.1@));
        r
    }

    pub open spec fn has_valid_paddr(self) -> bool {
        &&& self.paddr() < MAX_PADDR
        &&& self.paddr() % PAGE_SIZE == 0
    }

    pub open spec fn has_valid_ptr(self) -> bool {
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr()
        &&& self.ptr.addr() < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.ptr.addr() as Vaddr % META_SLOT_SIZE == 0
    }

    pub open spec fn paddr_spec(&self) -> Paddr {
        meta_to_page(self.ptr.addr() as Vaddr)
    }

    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn paddr(&self) ->(res: Paddr)
        requires
            self.has_valid_ptr(),
        ensures
            res == self.paddr_spec(),
            res % PAGE_SIZE == 0,
    {
        meta_to_page(self.ptr.addr() as Vaddr)
    }

    /// Forget the handle to the page.
    ///
    /// This will result in the page being leaked without calling the custom dropper.
    ///
    /// A physical address to the page is returned in case the page needs to be
    /// restored using [`Page::from_raw`] later. This is useful when some architectural
    /// data structures need to hold the page handle such as the page table.
    #[allow(unused)]
    pub fn into_raw(self, Tracked(s): Tracked<AbstractState>) -> (res: (Paddr, Tracked<AbstractState>))
    requires
        self.has_valid_ptr(),
        s.invariants(),
    ensures
        // Basic spec
        res.0 == self.paddr(),
        // Property 2: Usage Consistency
        res.1@.get_page(res.0).state == s.get_page((self.paddr()) as u64).state,
        // Property 3: Reference Counting Integrity
        res.1@.get_page(res.0).ref_count == s.get_page((self.paddr()) as u64).ref_count,
        // Property 4: Invariant Preservation
        res.1@.invariants(),
    {
        let paddr = self.paddr();
//        let slot = MetaSlot::concrete_from_paddr(paddr);
//        let Tracked(model) = Page::<M>::model_from_slot(slot);
//        assert (model == s.get_page(paddr)) by {
//            Page::<M>::model_from_slot_relate_abstract_data(paddr, &slot, &model, &s);
//        };
//        assert(s.get_page(paddr).invariants()) by {
//            self.lemma_has_valid_paddr_implies_get_page_satisfies_invariants(s);
//        };
        let ghost index = page_to_index(paddr);

        //core::mem::forget(self);
        forget_wrapper(self);
        (paddr, Tracked(s))


    }

    /// Restore a forgotten `Page` from a physical address.
    ///
    /// # Safety
    ///
    /// The caller should only restore a `Page` that was previously forgotten using
    /// [`Page::into_raw`].
    ///
    /// And the restoring operation should only be done once for a forgotten
    /// `Page`. Otherwise double-free will happen.
    ///
    /// Also, the caller ensures that the usage of the page is correct. There's
    /// no checking of the usage in this function.
    pub unsafe fn from_raw(paddr: Paddr, Tracked(s): Tracked<AbstractState>) -> (res: (Self, Tracked<AbstractState>))
        requires
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            s.invariants(),
            s.get_page(paddr).state != PageState::Unused,
        ensures
            res.0.paddr() == paddr,
            // Property 2: Usage Consistency
//            res.1@.get_page(res.0.paddr()).state == s.get_page(paddr).state,
            // Property 3: Reference Counting Integrity
//            res.1@.get_page(res.0.paddr()).ref_count == s.get_page(paddr).ref_count,
            // Property 4: Invariant Preservation
            res.1@.invariants(),
    {
        let vaddr = page_to_meta(paddr);
        let ptr = PPtr::from_usize(vaddr as usize);

        let p = Self {
                    ptr,
                    _marker: PhantomData,
                };

        proof{
            lemma_meta_to_page_bijectivity(paddr);
        }
        (Self{ptr, _marker: PhantomData}, Tracked(s))
    }

}

}
