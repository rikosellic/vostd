#![no_std]


pub struct DataCell {
    a: u32,
    b: u32,
}

pub struct Data<'a> {
    cell: &'a mut DataCell,
    total: u32
}

impl Data<'_> {
    pub fn feed_a(&mut self, i: u32) {
        self.cell.a += i;
        self.total += i;
    }

    pub fn a_to_b(self, i: u32) {
        self.cell.a -= i;
        self.cell.b += i;
    }
}