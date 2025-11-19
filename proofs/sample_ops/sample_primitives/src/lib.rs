use vstd::prelude::*;
use sample::*;
use sample_specs::*;



verus! {

pub mod proof_sample_primitives {
    use super::*;

    pub fn new() -> (res: Counter)
        ensures
            counter_inv(res),
        returns counter_new_spec(),
    {
        Counter { count: 0, step: 1 }
    }

    pub fn get_count(x: &Counter) -> (res: u64)
        returns
            x.count,
    {
        x.count
    }

    pub fn get_step(me: &Counter) -> (res: u64)
        returns
            me.step,
    {
        me.step
    }

    pub fn reset(me: &mut Counter)
        ensures
            me == counter_reset_spec(*old(me)),
    {
        me.count = 0;
    }

    pub fn set_step(me: &mut Counter, step: u64)
        requires
            step > 0,
        ensures
            me == counter_set_step_spec(*old(me), step)
    {
        // ensure the step is not zero to avoid infinite loops
        if step != 0 {
            me.step = step;
        }
    }

}


}