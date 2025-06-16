use vstd::prelude::*;
use sample::*;


verus! {

#[verifier::external_type_specification]
#[verifier::ext_equal]
pub struct ExCounter(pub Counter);

pub open spec fn counter_inv(c: Counter) -> bool {
    c.step > 0
}

pub open spec fn counter_new_spec() -> Counter {
    Counter { count: 0, step: 1 }
}

pub open spec fn counter_increment_spec(c: Counter) -> Counter {
    if c.count > u64::MAX - c.step {
        Counter { count: 0, step: c.step }
    } else {
        Counter { count: (c.count + c.step) as u64, step: c.step }
    }
}

pub open spec fn counter_reset_spec(c: Counter) -> Counter {
    Counter { count: 0, step: c.step }
}

pub open spec fn counter_set_step_spec(c: Counter, step: u64) -> Counter 
    recommends step > 0
{
    Counter { step, ..c }
}


}