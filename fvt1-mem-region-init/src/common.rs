use vstd::prelude::*;

verus! {

global layout usize is size == 8;

pub type Vaddr = usize;

// A casually defined number.
pub const MAX_PADDR: Vaddr = 0xffff_ffff;

pub const KERNEL_CODE_BASE_VADDR: Vaddr = 0xffff_ffff_8000_0000;

pub fn kernel_loaded_offset() -> Vaddr {
    KERNEL_CODE_BASE_VADDR
}

} // verus!
