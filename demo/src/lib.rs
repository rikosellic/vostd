#![no_std]

use vstd::prelude::*;
use vstd_extra::update_field;
use vstd::simple_pptr::*;
use aster_common::prelude::*;

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
        open spec fn inv(&self) -> bool { self.perm@.is_init() }
    }

    impl Inv for DataView {
        open spec fn inv(&self) -> bool { true }
    }

    impl InvView for DataOwner {
        type V = DataView;

        open spec fn view(&self) -> Self::V {
            DataView {
                cell: self.perm@.mem_contents().value()
            }
        }

        proof fn view_preserves_inv(&self) { }
    }

    impl OwnerOf for Data {
        type Owner = DataOwner;

        open spec fn wf(&self, owner: &Self::Owner) -> bool
        {
            owner.perm@.pptr() == self.cell
        }
    }

    impl ModelOf for Data { }
    }
}

mod specs {
    use super::*;

    verus! {
    impl Data {
        pub open spec fn a_to_b_precond(self, i: u32, cell_perm: PointsTo<DataCell>) -> bool
        {
            &&& cell_perm.mem_contents().value().a >= i
            &&& cell_perm.mem_contents().value().b + i <= u32::MAX
        }
    }
    }
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
            self.a_to_b_precond(i, old(own).perm@)
    {
        update_field!(self.cell => a -= i, own.perm.borrow_mut());
        update_field!(self.cell => b += i, own.perm.borrow_mut());
    }
}
}