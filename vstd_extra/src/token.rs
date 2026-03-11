use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Frac,Empty, FracGhost};
use crate::sum::*;

verus!{

/// A struct that stores and dispatches `FracGhost<T>`. 
/// Unlike `FracGhost`, it provides an `empty` state.
pub tracked struct FracGhostStorage<T, const TOTAL: u64> {
    tracked r: Option<FracGhost<T,TOTAL>>,
    ghost id: Loc,
}

impl <T, const TOTAL: u64> FracGhostStorage<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        self.r is Some ==> self.id == self.r->Some_0.id()
    }

    pub closed spec fn is_empty(self) -> bool {
        self.r is None
    }

    pub closed spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    /// Returns the `FracGhost<T,TOTAL>` stored in this `FracGhostStorage`.
    pub closed spec fn storage(self) -> FracGhost<T,TOTAL> 
    recommends self.not_empty()
    {
        self.r->Some_0
    }

    /// Returns the `T` stored in this `FracGhostStorage`.
    pub closed spec fn view(self) -> T 
    recommends self.not_empty()
    {
        self.storage().view()
    }

    pub open spec fn frac(self) -> int {
        if self.is_empty() {
            0int
        } else {
            self.storage().frac()
        }   
    }

    pub closed spec fn id(self) -> Loc {
        self.id
    }

    /*pub proof fn split_one(tracked &mut self) -> (tracked res: Frac<T,TOTAL>)
    requires
        old(self).not_empty(),
    ensures
        self.id() == old(self).id(),
        self.frac() + 1 == old(self).frac(),
        res.frac() == 1,
        res.id() == self.id(),
        res.resource() == old(self).resource(),
        old(self).frac() > 1 ==> self.resource() == old(self).resource(),
        old(self).frac() == 1 ==> self.is_empty(),
    {
        self.storage().bounded();
        if self.frac() == 1 {
            let r = self.
        }
    } */
}
}