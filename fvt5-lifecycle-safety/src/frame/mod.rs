pub mod model;
pub mod spec;

use core::mem::ManuallyDrop;
use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::simple_pptr;
use vstd::atomic::{PermissionU32};
use aster_common::prelude::*;
use vstd_extra::manually_drop;
use crate::common::*;
use crate::page::{*, model::*};
use model::*;
use spec::*;

verus! {

pub struct Frame {
    pub page: Page<FrameMeta>,
}

impl Frame {
    pub open spec fn inv(self) -> bool {
        self.page.inv_ptr()
    }

    pub open spec fn paddr_spec(&self) -> Paddr {
        self.page.paddr()
    }

    pub open spec fn end_paddr_spec(&self) -> Paddr {
        (self.page.paddr() + PAGE_SIZE_SPEC()) as usize
    }

    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn start_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            res == self.paddr_spec(),
            res % PAGE_SIZE_SPEC() == 0,
            res < MAX_PADDR_SPEC(),
    {
        self.page.paddr()
    }

    #[verifier::when_used_as_spec(end_paddr_spec)]
    pub fn end_paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            res == self.end_paddr_spec(),
            res % PAGE_SIZE_SPEC() == 0,
            res <= MAX_PADDR_SPEC(),
    {
        self.page.paddr() + PAGE_SIZE()
    }

    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.inv(),
        ensures
            res == self.paddr_spec(),
            res % PAGE_SIZE_SPEC() == 0,
            res < MAX_PADDR_SPEC(),
    {
        self.page.paddr()
    }

    pub fn reference_count<'a>(
        &'a self,
        p_slot: Tracked<&'a simple_pptr::PointsTo<MetaSlot>>,
        p_ref_count: Tracked<&PermissionU32>,
    ) -> (res: u32)
        requires
            self.inv(),
            p_slot@.pptr() == self.page.ptr,
            p_slot@.is_init(),
            p_ref_count@.is_for(p_slot@.value().ref_count),
        ensures
            res == p_ref_count@@.value,
    {
        self.page.reference_count(p_slot, p_ref_count)
    }

    #[rustc_allow_incoherent_impl]
    pub fn from(page: Page<FrameMeta>, Tracked(s): Tracked<AbstractState>) -> (res: (
        Self,
        Tracked<AbstractState>,
    ))
        requires
            page.has_valid_paddr(),
            page.relate_model(s.get_page(page.paddr())),
            s.get_page(page.paddr()).state == PageState::Untyped,
            s.get_page(page.paddr()).usage == PageUsage::Frame,
            exists|thread_id: int|
                s.get_page(page.paddr()).owners.contains(PageOwner::User { thread_id }),
            s.invariants(),
        ensures
            res.0.inv(),
            res.0.relate_model(res.1@.get_page(page.paddr())),
            res.1@.invariants(),
            res.1@ == s,
    {
        // Self { page }
        (Self { page }, Tracked(s))
    }

    #[rustc_allow_incoherent_impl]
    pub fn try_from(page: DynPage, Tracked(s): Tracked<AbstractState>) -> (res: (
        Result<Frame, DynPage>,
        Tracked<AbstractState>,
    ))
        requires
            page.inv_ptr(),
            page.relate_model(s.get_page(page.paddr())),
            s.invariants(),
            s.get_page(page.paddr()).state != PageState::Unused,
            s.get_page(page.paddr()).usage == PageUsage::Frame ==> s.get_page(page.paddr()).state
                == PageState::Untyped,
            s.get_page(page.paddr()).state == PageState::Untyped ==> exists|thread_id: int|
                s.get_page(page.paddr()).owners.contains(PageOwner::User { thread_id }),
        ensures
            res.0.is_ok() ==> res.0.get_Ok_0().relate_model(s.get_page(page.paddr())),
            res.0.is_err() ==> res.0.get_Err_0() == page,
            res.1@.invariants(),
            res.1@ == s,
    {
        //page.try_into().map(|p: Page<FrameMeta>| p.into())
        let (res, Tracked(s)) = page.try_into(Tracked(s));
        match res {
            Ok(p) => {
                let (p, Tracked(s)) = p.into_frame(Tracked(s));
                (Ok(p), Tracked(s))
            },
            Err(p) => (Err(p), Tracked(s)),
        }
    }
}

} // verus!
