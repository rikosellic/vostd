//! The "extra standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and general datatypes for proofs useful in Asterinas verification,
//! as well as extending [Verus standard library(vstd)](https://verus-lang.github.io/verus/verusdoc/vstd) with additional functionality.
#![allow(non_snake_case)]
#![feature(sized_hierarchy)]
#![feature(proc_macro_hygiene)]

pub mod vstd_extra;
pub mod align_ext;
pub mod aster_common;
pub mod ostd_specs;
pub mod ostd;
