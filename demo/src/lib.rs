#![no_std]

use vstd::prelude::*;
use vstd_extra::update_field;
use vstd::simple_pptr::*;

verus! {

pub struct DataCell {
    pub a: u32,
    pub b: u32,
}

pub struct Data {
    pub cell: PPtr<DataCell>,
}

impl Data {

    pub fn a_to_b(self, i: u32, Tracked(cell_perm): Tracked<&mut PointsTo<DataCell>>)
        requires
            old(cell_perm).pptr() == self.cell,
            old(cell_perm).mem_contents().is_init(),
            old(cell_perm).mem_contents().value().a >= i,
            old(cell_perm).mem_contents().value().b + i <= u32::MAX,
        ensures
            cell_perm.mem_contents().value().a + cell_perm.mem_contents().value().b ==
            old(cell_perm).mem_contents().value().a + old(cell_perm).mem_contents().value().b
    {
        update_field!(self.cell => a -= i, cell_perm);
        update_field!(self.cell => b += i, cell_perm);
    }
}
}