#![no_std]

pub struct DataCell<'a> {
    a: &'a mut u32,
    b: &'a mut u32,
}

impl DataCell<'_> {
    pub fn a_to_b(self, i: u32) {
        *self.a -= i;
        *self.b += i;
    }
}