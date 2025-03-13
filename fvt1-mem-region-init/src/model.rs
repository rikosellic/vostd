use vstd::prelude::*;

use super::common::MAX_PADDR;

verus! {

pub tracked struct MemRegionModel {
    pub ghost base: int,
    pub ghost end: int,
    pub ghost typ: int,
}

} // verus!
verus! {

impl MemRegionModel {
    pub open spec fn invariants(&self) -> bool {
        0 <= self.base <= self.end <= MAX_PADDR && 0 <= self.typ < 8
    }

    pub open spec fn is_sub_region(&self, old_region: &Self) -> bool {
        self.typ == old_region.typ && old_region.base <= self.base <= self.end <= old_region.end
    }

    pub open spec fn is_separate(&self, region: &Self) -> bool {
        self.end <= region.base || region.end <= self.base
    }
}

} // verus!
