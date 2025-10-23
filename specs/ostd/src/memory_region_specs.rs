extern crate vstd_extra;

use vstd::prelude::*;
use vstd_extra::prelude::*;
use aster_common::prelude::MAX_PADDR;

verus! {

pub ghost struct MemoryRegionModel {
    pub ghost base: int,
    pub ghost end: int,
    pub ghost typ: int,
}

impl MemoryRegionModel {
    pub open spec fn invariants(self) -> bool {
        0 <= self.base <= self.end <= MAX_PADDR() && 0 <= self.typ < 8
    }


}
}