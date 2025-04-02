// SPDX-License-Identifier: MPL-2.0

#![cfg_attr(not(test), no_std)]

use vstd::prelude::*;

verus! {
    pub fn align_down(x: usize, align: usize) -> usize
    {
        x - (x % align)
    }

}