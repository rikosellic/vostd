use vstd::prelude::*;
use aster_common::prelude::*;
use super::*;

verus! {

impl Frame {
    pub open spec fn into_raw_spec(
        self,
        thread_id: int,
        s1: AbstractState,
        s2: AbstractState,
    ) -> bool {
        let paddr = self.paddr();
        let model1 = s1.get_page(paddr);
        let model2 = s2.get_page(paddr);
        {
            &&& self.relate_model(model1)
            &&& model2.invariants()
            &&& s2.ghost_eq(s1.leak_owner_at_spec(paddr, PageOwner::User { thread_id }))
        }
    }
}

} // verus!
