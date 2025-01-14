pub mod model;

use vstd::prelude::*;
use aster_common::mm::Vaddr;

verus! {

pub enum PageTableError {
    /// The provided virtual address range is invalid.
    InvalidVaddrRange(Vaddr, Vaddr),
    /// The provided virtual address is invalid.
    InvalidVaddr(Vaddr),
    /// Using virtual address not aligned.
    UnalignedVaddr,
}

}