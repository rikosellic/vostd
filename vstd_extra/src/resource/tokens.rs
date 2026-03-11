use crate::sum::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Empty, Frac, FracGhost};

verus! {

/// A struct that stores and dispatches `FracGhost<T>`.
/// Unlike `FracGhost`, it provides an `empty` state.
pub tracked struct FracGhostStorage<T, const TOTAL: u64> {
    tracked r: Option<FracGhost<T, TOTAL>>,
    ghost snapshot: T,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> FracGhostStorage<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& self.r is Some ==> {
            &&& self.id == self.r->Some_0.id()
            &&& self.view() == self.r->Some_0@
        }
    }

    pub closed spec fn is_empty(self) -> bool {
        self.r is None
    }

    pub closed spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    pub closed spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    /// Returns the `FracGhost<T,TOTAL>` stored in this `FracGhostStorage`.
    pub closed spec fn storage(self) -> FracGhost<T, TOTAL>
        recommends
            self.not_empty(),
    {
        self.r->Some_0
    }

    /// Returns the `T` stored in this `FracGhostStorage`.
    pub closed spec fn view(self) -> T {
        self.snapshot
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

    pub proof fn new(value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
    {
        let tracked r = FracGhost::new(value);
        Self { r: Some(r), snapshot: value, id: r.id() }
    }

    pub proof fn split_one(tracked &mut self) -> (tracked res: FracGhost<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            self.id() == old(self).id(),
            self.frac() + 1 == old(self).frac(),
            self@ == old(self)@,
            res.frac() == 1,
            res.id() == self.id(),
            res@ == self@,
            old(self).frac() == 1 ==> self.is_empty(),
    {
        use_type_invariant(&*self);
        if self.frac() == 1 {
            self.r.tracked_take()
        } else {
            self.r.tracked_borrow().bounded();
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(1);
            self.r = Some(r);
            res
        }
    }

    pub proof fn split(tracked &mut self, n: int) -> (tracked res: FracGhost<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            self.id() == old(self).id(),
            self.frac() + n == old(self).frac(),
            self@ == old(self)@,
            res.frac() == n,
            res.id() == self.id(),
            res@ == self@,
            old(self).frac() == n ==> self.is_empty(),
    {
        use_type_invariant(&*self);
        self.r.tracked_borrow().bounded();
        if self.frac() == n {
            self.r.tracked_take()
        } else {
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(n);
            self.r = Some(r);
            res
        }
    }

    pub proof fn combine(tracked &mut self, tracked other: FracGhost<T, TOTAL>)
        requires
            old(self).id() == other.id(),
            other@ == old(self)@,
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self.frac() == old(self).frac() + other.frac(),
    {
        if self.is_empty() {
            other.bounded();
            self.r = Some(other);
        } else {
            use_type_invariant(&*self);
            let tracked mut r = self.r.tracked_take();
            r.combine(other);
            self.r = Some(r);
        }
    }

    pub proof fn bounded(tracked &self)
        ensures
            0 <= self.frac() <= TOTAL,
    {
        if self.not_empty() {
            self.r.tracked_borrow().bounded();
        }
    }

    pub proof fn update(tracked &mut self, value: T)
        requires
            old(self).is_full(),
        ensures
            self.is_full(),
            self@ == value,
            self.id() == old(self).id(),
    {
        use_type_invariant(&*self);
        let tracked mut r = self.r.tracked_take();
        r.update(value);
        self.snapshot = value;
        self.r = Some(r);
    }
}

pub type TokenStorage<const TOTAL: u64> = FracGhostStorage<(), TOTAL>;

pub type UniqueTokenStorage = TokenStorage<1>;

pub type Token<const TOTAL: u64> = FracGhost<(), TOTAL>;

pub type UniqueToken = Token<1u64>;

} // verus!
