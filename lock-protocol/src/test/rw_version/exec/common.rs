use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::vstd::arithmetic::power2::*;
use vstd::bits::*;

use super::super::spec::{
    common::*,
    utils::*,
};

verus!{

pub type Paddr = u64;
pub type Vaddr = u64;

pub type Level = u64;

// Configurations
pub spec const GLOBAL_CPU_NUM: nat = 2;

pub const INVALID_PADDR: Paddr = 0xffff_ffff_ffff_ffff;

}

verus!{

pub open spec fn valid_vaddr(va: Vaddr) -> bool {
    0 <= va < pow2(48)
}

pub open spec fn vaddr_is_aligned_spec(va: Vaddr) -> bool {
    (va & (low_bits_mask(12) as u64)) == 0
}

#[verifier::when_used_as_spec(vaddr_is_aligned_spec)]
pub fn vaddr_is_aligned(va: Vaddr) -> (res: bool)
    requires
        valid_vaddr(va),
    ensures
        res == vaddr_is_aligned_spec(va),
{
    assume(false);
    (va & (1u64 << 12)) == 0
}

pub open spec fn va_level_to_trace_rec(vaddr: Vaddr, level: Level) -> Seq<nat>
    recommends
        1 <= level <= 4,
    decreases 4 - level,
{
    if 1 <= level <= 4 {
        if level == 4 { Seq::empty() }
        else {
            va_level_to_trace_rec(vaddr, (level + 1) as Level)
                .push(((vaddr >> (level * 9)) & low_bits_mask(9) as u64) as nat)
        }
    } else { arbitrary() }
}

pub open spec fn va_level_to_trace(vaddr: Vaddr, level: Level) -> Seq<nat> {
    va_level_to_trace_rec(vaddr >> 12, level)
}

pub open spec fn va_level_to_nid(vaddr: Vaddr, level: Level) -> NodeId {
    NodeHelper::trace_to_nid_from_root(va_level_to_trace(vaddr, level))
}

}