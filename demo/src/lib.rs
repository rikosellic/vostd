#![no_std]

use aster_common::prelude::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd_extra::update_field;

mod common {
    use super::*;

    verus! {

pub struct DataCell {
    pub a: u32,
    pub b: u32,
}

pub struct Data {
    pub cell: PPtr<DataCell>,
}

pub ghost struct DataView {
    pub cell: DataCell,
}

pub tracked struct DataOwner {
    pub perm: Tracked<PointsTo<DataCell>>,
}

impl Inv for DataOwner {
    open spec fn inv(&self) -> bool {
        self.perm@.is_init()
    }
}

impl Inv for DataView {
    open spec fn inv(&self) -> bool {
        true
    }
}

impl InvView for DataOwner {
    type V = DataView;

    open spec fn view(&self) -> Self::V {
        DataView { cell: self.perm@.mem_contents().value() }
    }

    proof fn view_preserves_inv(&self) {
    }
}

impl OwnerOf for Data {
    type Owner = DataOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        owner.perm@.pptr() == self.cell
    }
}

impl ModelOf for Data {

}

} // verus!
}

mod specs {
    use super::*;

    verus! {

impl Data {
    pub open spec fn a_to_b_precond(self, i: u32, cell_perm: PointsTo<DataCell>) -> bool {
        &&& cell_perm.mem_contents().value().a >= i
        &&& cell_perm.mem_contents().value().b + i <= u32::MAX
    }

    pub open spec fn a_to_b_spec(self, i: u32, old_cell: DataView, new_cell: DataView) -> bool {
        old_cell.cell.a + old_cell.cell.b == new_cell.cell.a + new_cell.cell.b
    }
}

} // verus!
}

use common::*;
use specs::*;

verus! {

impl Data {
    #[verus_spec(
        with Tracked(own): Tracked<&mut DataOwner>
    )]
    pub fn a_to_b(self, i: u32)
        requires
            old(own).inv(),
            self.wf(old(own)),
            self.a_to_b_precond(i, old(own).perm@),
        ensures
            self.a_to_b_spec(i, self.model(old(own)), self.model(own)),
    {
        update_field!(self.cell => a -= i; own.perm.borrow_mut());
        update_field!(self.cell => b += i; own.perm.borrow_mut());
    }
}

} // verus!
