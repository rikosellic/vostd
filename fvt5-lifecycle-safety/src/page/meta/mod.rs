extern crate vstd_extra;
pub mod model;
//pub mod impls;
//pub mod specs;

use core::{mem::ManuallyDrop, mem::size_of, cell::UnsafeCell};
use vstd::{prelude::*, cell::*, atomic::*, atomic_ghost::*};
