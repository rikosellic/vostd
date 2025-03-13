use vstd::prelude::*;
use core::mem::ManuallyDrop;
use core::mem::forget;

verus! {

#[verifier::external_body]
pub fn manually_drop<T>(x: T) -> (res: ManuallyDrop<T>) {
    ManuallyDrop::new(x)
}

#[verifier::external_body]
pub fn forget_wrapper<T>(t: T) {
    forget(t)
}

#[verifier::external_body]
pub fn spin_loop() {
    core::hint::spin_loop();
}

} // verus!
