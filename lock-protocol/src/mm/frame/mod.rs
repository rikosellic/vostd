pub mod meta;
pub mod untyped;

use std::marker::PhantomData;

use meta::AnyFrameMeta;
use meta::GetFrameError;
use meta::MetaSlot;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::mm::Paddr;
use crate::mm::PagingLevel;
use crate::mm::PAGE_SIZE;

verus! {

// #[repr(transparent)] TODO: repr(transparent)
// pub struct Frame<M: AnyFrameMeta + ?Sized> {
pub struct Frame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

impl<M: AnyFrameMeta> Frame<M> {
    /// Gets a [`Frame`] with a specific usage from a raw, unused page.
    ///
    /// The caller should provide the initial metadata of the page.
    ///
    /// If the provided frame is not truly unused at the moment, it will return
    /// an error. If wanting to acquire a frame that is already in use, use
    /// [`Frame::from_in_use`] instead.
    // TODO: Implement MetaSlot::get_from_unused
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
        Ok(Self {
            // ptr: MetaSlot::get_from_unused(paddr, metadata, false)?,
            ptr: PPtr::<MetaSlot>::empty().0,
            _marker: PhantomData,
        })
    }

    /// Gets the metadata of this page.
    // TODO: Implement Frame::meta
    #[verifier::external_body]
    pub fn meta(&self) -> &M {
        // SAFETY: The type is tracked by the type system.
        // unsafe { &*self.slot().as_meta_ptr::<M>() }
        unimplemented!("Frame::meta")
    }
}

// impl Frame<dyn AnyFrameMeta> {
//     /// Gets a dynamically typed [`Frame`] from a raw, in-use page.
//     ///
//     /// If the provided frame is not in use at the moment, it will return an error.
//     ///
//     /// The returned frame will have an extra reference count to the frame.
//     pub fn from_in_use(paddr: Paddr) -> Result<Self, GetFrameError> {
//         // Ok(Self {
//         //     ptr: MetaSlot::get_from_in_use(paddr)?,
//         //     _marker: PhantomData,
//         // })
//         unimplemented!("Frame::from_in_use")
//     }
// }

// impl<M: AnyFrameMeta + ?Sized> Frame<M> {
impl<M: AnyFrameMeta> Frame<M> {

    /// Gets the physical address of the start of the frame.
    // TODO: Implement
    #[verifier::external_body]
    pub fn start_paddr(&self) -> Paddr {
        // self.slot().frame_paddr()
        unimplemented!("Frame::start_paddr")
    }

    /// Gets the paging level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    #[verifier::when_used_as_spec(map_level_spec)]
    pub const fn map_level(&self) -> (res: PagingLevel)
    ensures
        res == 1,
        res == self.map_level_spec(),
    {
        1
    }

    pub open spec fn map_level_spec(&self) -> PagingLevel {
        1
    }

    /// Gets the size of this page in bytes.
    #[verifier::when_used_as_spec(size_spec)]
    pub const fn size(&self) -> (res: usize)
    ensures
        res == PAGE_SIZE,
        res == self.size_spec(),
    {
        PAGE_SIZE
    }

    pub open spec fn size_spec(&self) -> usize {
        PAGE_SIZE
    }

    /// Gets the dyncamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.
    // pub fn dyn_meta(&self, perm: PointsTo<MetaSlot>) -> &dyn AnyFrameMeta {
    // TODO: Implement
    #[verifier::external_body]
    pub fn dyn_meta<T: AnyFrameMeta>(&self, perm: PointsTo<MetaSlot>) -> &T {
        // SAFETY: The metadata is initialized and valid.
        // unsafe { &*self.slot(perm).dyn_meta_ptr() }
        unimplemented!("Frame::dyn_meta")
    }

    /// Gets the reference count of the frame.
    ///
    /// It returns the number of all references to the frame, including all the
    /// existing frame handles ([`Frame`], [`Frame<dyn AnyFrameMeta>`]), and all
    /// the mappings in the page table that points to the frame.
    ///
    /// # Safety
    ///
    /// The function is safe to call, but using it requires extra care. The
    /// reference count can be changed by other threads at any time including
    /// potentially between calling this method and acting on the result.
    /// TODO: Implement Frame::reference_count
    // pub fn reference_count(&self) -> u64 {
    //     let refcnt = self.slot().ref_count.load(Ordering::Relaxed);
    //     debug_assert!(refcnt < meta::REF_COUNT_MAX);
    //     refcnt
    // }

    /// Forgets the handle to the frame.
    ///
    /// This will result in the frame being leaked without calling the custom dropper.
    ///
    /// A physical address to the frame is returned in case the frame needs to be
    /// restored using [`Frame::from_raw`] later. This is useful when some architectural
    /// data structures need to hold the frame handle such as the page table.
    /// TODO: Implement Frame::into_raw
    // pub(in crate::mm) fn into_raw(self) -> Paddr {
    //     let this = ManuallyDrop::new(self);
    //     this.start_paddr()
    // }

    /// Restores a forgotten [`Frame`] from a physical address.
    ///
    /// # Safety
    ///
    /// The caller should only restore a `Frame` that was previously forgotten using
    /// [`Frame::into_raw`].
    ///
    /// And the restoring operation should only be done once for a forgotten
    /// [`Frame`]. Otherwise double-free will happen.
    ///
    /// Also, the caller ensures that the usage of the frame is correct. There's
    /// no checking of the usage in this function.
    /// TODO: Implement Frame::from_raw
    pub(in crate::mm) fn from_raw(paddr: Paddr) -> Self {
        // let vaddr = mapping::frame_to_meta::<PagingConsts>(paddr);
        // let ptr = vaddr as *const MetaSlot;

        // Self {
        //     ptr,
        //     _marker: PhantomData,
        // }
        Self {
            ptr: PPtr::<MetaSlot>::from_addr(paddr),
             _marker: PhantomData
        }
    }

    // TODO: Implement slot for Frame
    fn slot<'a>(&'a self, perm: Tracked<&'a PointsTo<MetaSlot>>) -> &'a MetaSlot
    requires
        perm@.pptr() == self.ptr,
        perm@.is_init()
    {
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        // unsafe { &*self.ptr }
        self.ptr.borrow(perm)
    }
}

}
