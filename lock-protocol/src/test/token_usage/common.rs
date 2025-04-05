use builtin::*;
use builtin_macros::*;

verus!{

pub type Paddr = u64;
pub type Vaddr = u64;

pub type PtLevel = u64;

pub open spec fn valid_paddr(paddr: Paddr) -> bool { true }

pub tracked struct PagePerm {
    pub paddr: Paddr,
}

}