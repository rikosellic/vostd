use vstd::prelude::*;

use crate::mm::{meta::AnyFrameMeta, Frame};

verus! {

    /// The metadata of untyped frame.
    ///
    /// If a structure `M` implements [`AnyUFrameMeta`], it can be used as the
    /// metadata of a type of untyped frames [`Frame<M>`]. All frames of such type
    /// will be accessible as untyped memory.
    pub trait AnyUFrameMeta: AnyFrameMeta {}

    /// A smart pointer to an untyped frame with any metadata.
    ///
    /// The metadata of the frame is not known at compile time but the frame must
    /// be an untyped one. An [`UFrame`] as a parameter accepts any type of
    /// untyped frame metadata.
    ///
    /// The usage of this frame will not be changed while this object is alive.
    pub type UFrame = Frame<dyn AnyUFrameMeta>;

    /// Makes a structure usable as untyped frame metadata.
    ///
    /// Directly implementing [`AnyFrameMeta`] is not safe since the size and
    /// alignment must be checked. This macro provides a safe way to implement both
    /// [`AnyFrameMeta`] and [`AnyUFrameMeta`] with compile-time checks.
    ///
    /// If this macro is used for built-in typed frame metadata, it won't compile.
    #[macro_export]
    macro_rules! impl_untyped_frame_meta_for {
        // Implement without specifying the drop behavior.
        ($t:ty) => {
            // use static_assertions::const_assert;
            // const_assert!(size_of::<$t>() <= $crate::mm::frame::meta::FRAME_METADATA_MAX_SIZE);
            // const_assert!(align_of::<$t>() <= $crate::mm::frame::meta::FRAME_METADATA_MAX_ALIGN);
            // TODO: Fix assertions
            // SAFETY: The size and alignment of the structure are checked.
            // unsafe
            impl $crate::mm::frame::meta::AnyFrameMeta for $t {
                // TODO: Implement is_untyped
                // fn is_untyped(&self) -> bool {
                //     true
                // }
            }
            impl $crate::mm::frame::untyped::AnyUFrameMeta for $t {}
        };
        // Implement with a customized drop function.
        ($t:ty, $body:expr) => {
            // use static_assertions::const_assert;
            // const_assert!(size_of::<$t>() <= $crate::mm::frame::meta::FRAME_METADATA_MAX_SIZE);
            // const_assert!(align_of::<$t>() <= $crate::mm::frame::meta::FRAME_METADATA_MAX_ALIGN);
            // TODO: Fix assertions
            // SAFETY: The size and alignment of the structure are checked.
            // Outside OSTD the user cannot implement a `on_drop` method for typed
            // frames. And untyped frames can be safely read.
            unsafe impl $crate::mm::frame::meta::AnyFrameMeta for $t {
                // TODO: Implement on_drop
                // fn on_drop(&mut self, reader: &mut $crate::mm::VmReader<$crate::mm::Infallible>) {
                //     $body
                // }

                // TODO: Implement is_untyped
                // fn is_untyped(&self) -> bool {
                //     true
                // }
            }
            impl $crate::mm::frame::untyped::AnyUFrameMeta for $t {}
        };
    }

    // A special case of untyped metadata is the unit type.
    impl_untyped_frame_meta_for!(());
}
