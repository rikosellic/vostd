#![no_std]

mod ptr_extra;
use ptr_extra::*;

pub struct DataCell {
    a: u32,
    b: u32,
}

pub struct Data<'a> {
    cell: &'a mut DataCell,
}

impl Data<'_> {
    pub fn a_to_b(self, i: u32) {
        update_field!(self.cell => a -= i);
        update_field!(self.cell => b += i);
    }
}