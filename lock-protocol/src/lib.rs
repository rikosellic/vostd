<<<<<<< HEAD
=======

>>>>>>> Temp
// #![feature(generic_const_exprs)]
#![allow(unused)]
#![feature(slice_ptr_get)]
#![feature(strict_provenance)]
#![feature(core_intrinsics)]
#![allow(non_snake_case)]
#![feature(sync_unsafe_cell)]
<<<<<<< HEAD
#![allow(type_alias_bounds)]

pub mod mm;
pub mod prelude;
pub mod spec;
// pub mod test;
=======

pub mod mm;
pub mod spec;
pub mod prelude;
pub mod test;
>>>>>>> Temp
pub mod task;
pub mod x86_64;
#[macro_use]
pub mod helpers;
pub mod sync;

<<<<<<< HEAD
pub mod exec;

fn main() {
    exec::main_test();
}
=======
fn main() {
    spec::simple_page_table::main();
}
>>>>>>> Temp
