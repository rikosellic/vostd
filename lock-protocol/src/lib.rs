
// #![feature(generic_const_exprs)]
#![allow(unused)]
#![feature(slice_ptr_get)]
#![feature(strict_provenance)]
#![feature(core_intrinsics)]

pub mod mm;
pub mod spec;
pub mod prelude;

#[allow(unused_imports)]
pub use mm::*;