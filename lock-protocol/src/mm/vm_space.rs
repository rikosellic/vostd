// SPDX-License-Identifier: MPL-2.0

//! Virtual memory space management.
//!
//! The [`VmSpace`] struct is provided to manage the virtual memory space of a
//! user. Cursors are used to traverse and modify over the virtual memory space
//! concurrently. The VM space cursor [`self::Cursor`] is just a wrapper over
//! the page table cursor [`super::page_table::Cursor`], providing efficient,
//! powerful concurrent accesses to the page table, and suffers from the same
//! validity concerns as described in [`super::page_table::cursor`].

use core::{ops::Range, sync::atomic::Ordering};
use vstd::prelude::*;

verus! {

use vstd::prelude::verus;

use super::PAGE_SIZE;

// TODO: VmSpace
// TODO: Cursor
// TODO: CursorMut
// TODO: cpu_local_cell!
// TODO: VmItem

/// A token that can be used to mark a slot in the VM space.
///
/// The token can be converted to and from a [`usize`] value. Available tokens
/// are non-zero and capped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token(usize);

impl Token {
    /// The mask that marks the available bits in a token.
    // const MASK: usize = ((1 << 39) - 1) / PAGE_SIZE;

    pub open spec fn MASK_SPEC() -> usize {
        (((1 << 39) as usize - 1) / PAGE_SIZE as int) as usize
    }

    pub fn MASK() -> usize {
        ((1 << 39) - 1) / PAGE_SIZE
    }

    pub(crate) fn into_raw_inner(self) -> usize {
        self.0
    }

    /// Creates a new token from a raw value.
    ///
    /// # Safety
    ///
    /// The raw value must be a valid token created by [`Self::into_raw_inner`].
    pub(crate) fn from_raw_inner(raw: usize) -> Self
    requires
        raw & Self::MASK_SPEC() == 0,
    {
        Self(raw)
    }
}

impl TryFrom<usize> for Token {
    type Error = ();

    fn try_from(value: usize) -> core::result::Result<Self, Self::Error> {
        if value & Self::MASK() == 0 || value != 0 {
            Ok(Self(value * PAGE_SIZE))
        } else {
            Err(())
        }
    }
}

impl From<Token> for usize {
    fn from(token: Token) -> usize {
        token.0 / PAGE_SIZE
    }
}

// TODO: TryFrom<PageTableItem> for VmItem

}
