use vstd::prelude::*;

verus! {

pub open spec fn expect_spec<T, E: core::fmt::Debug>(result: Result<T, E>, msg: &str) -> T
    recommends
        result.is_Ok(),
{
    result.get_Ok_0()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(expect_spec)]
pub fn expect<T, E: core::fmt::Debug>(result: Result<T, E>, msg: &str) -> T
    requires
        result.is_Ok(),
{
    result.expect(msg)
}

} // verus!
