// SPDX-License-Identifier: MPL-2.0
//! Definitions of page mapping properties.
use core::fmt::Debug;

pub use crate::aster_common::prelude::*;

impl PageProperty {
    /// Creates a new `PageProperty` with the given flags and cache policy for the user.
    #[rustc_allow_incoherent_impl]
    pub fn new_user(flags: PageFlags, cache: CachePolicy) -> Self {
        Self {
            flags,
            cache,
            priv_flags: PrivilegedPageFlags::USER(),
        }
    }

    /// Creates a page property that implies an invalid page without mappings.
    #[rustc_allow_incoherent_impl]
    pub fn new_absent() -> Self {
        Self {
            flags: PageFlags::empty(),
            cache: CachePolicy::Writeback,
            priv_flags: PrivilegedPageFlags::empty(),
        }
    }
}
