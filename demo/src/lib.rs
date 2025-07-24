#![no_std]

mod ptr_extra;
use ptr_extra::*;

pub struct DataCell<'a> {
    a: &'a mut u32,
    b: &'a mut u32,

    total: u32,
}

impl DataCell<'_> {
    pub fn a_to_b(self, i: u32) {
        update_field!(self => a -= i, &mut);
        update_field!(self => b += i, &mut);
    }
}