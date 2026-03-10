use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Frac,Empty};
use crate::sum::*;

verus!{

/// A struct that stores and dispatches `Frac<T>`.
pub tracked struct FracStorage<T, const TOTAL: u64> {
    pub tracked resource: Sum<Frac<T,TOTAL>, Empty<T,TOTAL>>
}

impl <T, const TOTAL: u64> FracStorage<T, TOTAL> {    
    pub open spec fn is_empty(self) -> bool {
        self.resource is Right
    }

    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    pub open spec fn storage(self) -> Frac<T,TOTAL> 
    recommends self.not_empty()
    {
        self.resource->Left_0
    }

    pub open spec fn frac(self) -> int {
        if self.is_empty() {
            0int
        } else {
            self.storage().frac()
        }   
    }

    pub open spec fn id(self) -> Loc {
        if self.is_empty() {
            self.resource -> Right_0.id()
        }
        else {
            self.storage().id()
        }
    }
} 

pub type TokenStorage<const TOTAL: u64> = FracStorage<(), TOTAL>;

pub type SingleTokenStorage = TokenStorage<1>;

}