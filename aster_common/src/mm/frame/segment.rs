use vstd::prelude::*;

use core::ops::Range;

use super::*;

verus! {

/// A contiguous range of homogeneous physical memory frames.
///
/// This is a handle to multiple contiguous frames. It will be more lightweight
/// than owning an array of frame handles.
///
/// The ownership is achieved by the reference counting mechanism of frames.
/// When constructing a [`Segment`], the frame handles are created then
/// forgotten, leaving the reference count. When dropping a it, the frame
/// handles are restored and dropped, decrementing the reference count.
///
/// All the metadata of the frames are homogeneous, i.e., they are of the same
/// type.
#[repr(transparent)]
#[rustc_has_incoherent_inherent_impls]
pub struct Segment<M: AnyFrameMeta + ?Sized> {
    /// The physical address range of the segment.
    pub range: Range<Paddr>,
    /// Marker for the metadata type.
    pub _marker: core::marker::PhantomData<M>,
}

/// A [`SegmentOnwer<M>`] holds the permission tokens for all frames in the
/// [`Segment<M>`] for verification purposes.
pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    pub perms: Seq<FramePerm<M>>,
}

impl<M: AnyFrameMeta + ?Sized> Inv for Segment<M> {
    /// The invariant of a [`Segment`].
    open spec fn inv(&self) -> bool {
        &&& self.range.start % PAGE_SIZE() == 0
        &&& self.range.end % PAGE_SIZE() == 0
        &&& self.range.start <= self.range.end < MAX_PADDR()
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    pub open spec fn inv_with(&self, owner: &SegmentOwner<M>) -> bool {
        &&& self.inv()
        &&& owner.perms.len() * PAGE_SIZE() == self.range.end - self.range.start
        &&& forall|i: int|
            #![trigger owner.perms[i]]
            0 <= i < owner.perms.len() as int ==> owner.perms[i].addr() == self.range.start + (
            i as u64) * PAGE_SIZE()
    }
}

} // verus!
