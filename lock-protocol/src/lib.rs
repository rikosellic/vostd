
// #![feature(generic_const_exprs)]
#![allow(unused)]
#![feature(slice_ptr_get)]
#![feature(strict_provenance)]
#![feature(core_intrinsics)]
#![allow(non_snake_case)]
#![feature(sync_unsafe_cell)]

pub mod mm;
pub mod spec;
pub mod prelude;
pub mod test;
pub mod task;
pub mod x86_64;
#[macro_use]
pub mod helpers;
pub mod sync;

fn main() {
    spec::simple_page_table::main();
}