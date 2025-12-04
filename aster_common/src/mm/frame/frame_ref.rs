use vstd::prelude::*;

use std::ops::Deref;

use core::mem::ManuallyDrop;

use vstd_extra::manually_drop::*;

use super::*;

verus! {

/// A struct that can work as `&'a Frame<M>`.
#[rustc_has_incoherent_inherent_impls]
pub struct FrameRef<'a, M: AnyFrameMeta> {
    pub inner: ManuallyDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<M: AnyFrameMeta> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(ensures returns manually_drop_deref_spec(&self.inner))]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

} // verus!
