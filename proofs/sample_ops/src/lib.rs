use vstd::prelude::*;
use sample::*;
use sample_specs::*;



verus! {

pub mod proof_sample_ops {
    use super::*;

    pub assume_specification[Counter::get_count](
        me: &Counter
    ) -> (res: u64)
        ensures
            res == me.count,
    ;

    pub assume_specification[Counter::get_step](
        me: &Counter
    ) -> (res: u64)
        ensures
            res == me.step,
    ;


    pub fn increment(me: &mut Counter)
        requires
            counter_inv(*old(me)),
        ensures
            me == counter_increment_spec(*old(me)),
            counter_inv(*me),
    {
        if me.get_count() > u64::MAX - me.get_step() {
            me.count = 0;
        } else {
            me.count = me.get_count() + me.get_step();
        }
    }

}


}