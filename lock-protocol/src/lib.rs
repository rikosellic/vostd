
// #![feature(generic_const_exprs)]
#![allow(unused)]
#![feature(slice_ptr_get)]
#![feature(strict_provenance)]
#![feature(core_intrinsics)]
#![allow(non_snake_case)]

pub mod mm;
pub mod spec;
pub mod prelude;
pub mod test;

fn main() {
    spec::simple_page_table::main();
}