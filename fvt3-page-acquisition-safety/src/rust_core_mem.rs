use vstd::prelude::*;
use core::mem::ManuallyDrop;

verus! {

#[verifier::external_body]
pub fn manually_drop<T>(x: T) -> (res: ManuallyDrop<T>) {
    ManuallyDrop::new(x)
}

} // verus!
