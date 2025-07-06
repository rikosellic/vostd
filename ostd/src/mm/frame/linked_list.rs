// SPDX-License-Identifier: MPL-2.0

//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.

use vstd::prelude::*;
use vstd::simple_pptr::*;

use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

use super::{
    mapping,
    meta::{get_slot},
    MetaSlot,
};

use aster_common::prelude::{meta, Link, UniqueFrameLink, FrameMeta};

use crate::{
    arch::mm::PagingConsts,
    mm::{Paddr, Vaddr},
//    panic::abort,
};

verus! {

impl MetaSlot {
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    pub fn in_list_load(self) -> u64 {
        unimplemented!()
    }

    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    pub fn in_list_store(&mut self, i: u64) {
        unimplemented!()
    }
}

/// A linked list of frames.
///
/// Two key features that [`LinkedList`] is different from
/// [`alloc::collections::LinkedList`] is that:
///  1. It is intrusive, meaning that the links are part of the frame metadata.
///     This allows the linked list to be used without heap allocation. But it
///     disallows a frame to be in multiple linked lists at the same time.
///  2. The linked list exclusively own the frames, meaning that it takes
///     unique pointers [`UniqueFrame`]. And other bodies cannot
///     [`from_in_use`] a frame that is inside a linked list.
///  3. We also allow creating cursors at a specific frame, allowing $O(1)$
///     removal without iterating through the list at a cost of some checks.
///
/// # Example
///
/// To create metadata types that allows linked list links, wrap the metadata
/// type in [`Link`]:
///
/// ```rust
/// use ostd::{
///     mm::{frame::{linked_list::{Link, LinkedList}, Frame}, FrameAllocOptions},
///     impl_untyped_frame_meta_for,
/// };
///
/// #[derive(Debug)]
/// struct MyMeta { mark: usize }
///
/// type MyFrame = Frame<Link<MyMeta>>;
///
/// impl_untyped_frame_meta_for!(MyMeta);
///
/// let alloc_options = FrameAllocOptions::new();
/// let frame1 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 1 })).unwrap();
/// let frame2 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 2 })).unwrap();
///
/// let mut list = LinkedList::new();
/// list.push_front(frame1.try_into().unwrap());
/// list.push_front(frame2.try_into().unwrap());
///
/// let mut cursor = list.cursor_front_mut();
/// assert_eq!(cursor.current_meta().unwrap().mark, 2);
/// cursor.move_next();
/// assert_eq!(cursor.current_meta().unwrap().mark, 1);
/// ```
///
/// [`from_in_use`]: Frame::from_in_use
pub struct LinkedList
{
    front: Option<PPtr<Link>>,
    back: Option<PPtr<Link>>,
    /// The number of frames in the list.
    size: usize,
    /// A lazily initialized ID, used to check whether a frame is in the list.
    /// 0 means uninitialized.
    list_id: u64,
}

// SAFETY: Only the pointers are not `Send` and `Sync`. But our interfaces
// enforces that only with `&mut` references can we access with the pointers.
//unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
//unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}

impl Default for LinkedList
{
    fn default() -> Self {
        Self::new()
    }
}

impl LinkedList
{
    /// Creates a new linked list.
    pub const fn new() -> Self {
        Self {
            front: None,
            back: None,
            size: 0,
            list_id: 0,
        }
    }

    /// Gets the number of frames in the linked list.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Tells if the linked list is empty.
    pub fn is_empty(&self) -> bool {
        let is_empty = self.size == 0;
//        debug_assert_eq!(is_empty, self.front.is_none());
//        debug_assert_eq!(is_empty, self.back.is_none());
        is_empty
    }

    #[verifier::external_body]
    /// Pushes a frame to the front of the linked list.
    pub fn push_front(&mut self, frame: UniqueFrameLink) {
        unimplemented!()
//        self.cursor_front_mut().insert_before(frame);
    }

    #[verifier::external_body]
    /// Pops a frame from the front of the linked list.
    pub fn pop_front(&mut self) -> Option<UniqueFrameLink> {
        unimplemented!()
//        self.cursor_front_mut().take_current()
    }

    #[verifier::external_body]
    /// Pushes a frame to the back of the linked list.
    pub fn push_back(&mut self, frame: UniqueFrameLink) {
        unimplemented!()
//        self.cursor_at_ghost_mut().insert_before(frame);
    }

    #[verifier::external_body]
    /// Pops a frame from the back of the linked list.
    pub fn pop_back(&mut self) -> Option<UniqueFrameLink> {
        unimplemented!()
//        self.cursor_back_mut().take_current()
    }

    /// Tells if a frame is in the list.
    #[verifier::external_body]
    pub fn contains(&mut self, frame: Paddr) -> bool {
        unimplemented!()
/*        let Ok(slot) = get_slot(frame) else {
            return false;
        };
//        slot.in_list.load(Ordering::Relaxed) == self.lazy_get_id()
        slot.in_list_load() == self.lazy_get_id()*/
    }

    #[verifier::external_body]
    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fail if [`Self::contains`] returns `false`.
    pub fn cursor_mut_at(&mut self, frame: Paddr) -> Option<CursorMut> {
        unimplemented!()
        /*
        let Ok(slot) = get_slot(frame) else {
            return None;
        };
//        let contains = slot.in_list.load(Ordering::Relaxed) == self.lazy_get_id();
        let contains = slot.in_list_load() == self.lazy_get_id();
        if contains {
            Some(CursorMut {
                list: self,
                current: Some(slot.as_meta_ptr()),
            })
        } else {
            None
        }*/
    }

    #[verifier::external_body]
    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    pub fn cursor_front_mut(&mut self) -> CursorMut {
        unimplemented!()
        /*
        let current = self.front;
        CursorMut {
            list: self,
            current,
        }
        */
    }

    #[verifier::external_body]
    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    pub fn cursor_back_mut(&mut self) -> CursorMut {
        unimplemented!()
        /*
        let current = self.back;
        CursorMut {
            list: self,
            current,
        }
        */
    }

    #[verifier::external_body]
    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    fn cursor_at_ghost_mut(&mut self) -> CursorMut {
        unimplemented!()
        /*
        CursorMut {
            list: self,
            current: None,
        }
        */
    }

    #[verifier::external_body]
    fn lazy_get_id(&mut self) -> u64 {
        // FIXME: Self-incrementing IDs may overflow, while `core::pin::Pin`
        // is not compatible with locks. Think about a better solution.
        static LIST_ID_ALLOCATOR: AtomicU64 = AtomicU64::new(1);
        const MAX_LIST_ID: u64 = i64::MAX as u64;

        if self.list_id == 0 {
            let id = LIST_ID_ALLOCATOR.fetch_add(1, Ordering::Relaxed);
            if id >= MAX_LIST_ID {
//                log::error!("The frame list ID allocator has exhausted.");
//                abort();
                unimplemented!()
            }
            self.list_id = id;
            id
        } else {
            self.list_id
        }
    }
}

}

verus!{

/// A cursor that can mutate the linked list links.
///
/// The cursor points to either a frame or the "ghost" non-element. It points
/// to the "ghost" non-element when the cursor surpasses the back of the list.
pub struct CursorMut
{
    list: PPtr<LinkedList>,
    current: Option<PPtr<Link>>,
}

impl FrameMeta {
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    pub fn to_vaddr(&self) -> Vaddr {
        unimplemented!()
    }
}

impl CursorMut
{
/*    /// Moves the cursor to the next frame towards the back.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the first element of the [`LinkedList`]. If it is pointing
    /// to the last element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    pub fn move_next(&mut self) {
        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => unsafe { current.as_ref().next },
            None => self.list.front,
        };
    }

    /// Moves the cursor to the previous frame towards the front.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the last element of the [`LinkedList`]. If it is pointing
    /// to the first element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    pub fn move_prev(&mut self) {
        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => unsafe { current.as_ref().prev },
            None => self.list.back,
        };
    }*/

    /*
    /// Gets the mutable reference to the current frame's metadata.
    pub fn current_meta(&mut self) -> Option<&mut M> {
        self.current.map(|current| {
            // SAFETY: `&mut self` ensures we have exclusive access to the
            // frame metadata.
            let link_mut = unsafe { &mut *current.as_ptr() };
            // We should not allow `&mut Link<M>` to modify the original links,
            // which would break the linked list. So we just return the
            // inner metadata `M`.
            &mut link_mut.meta
        })
    }
    */

    /// Takes the current pointing frame out of the linked list.
    ///
    /// If successful, the frame is returned and the cursor is moved to the
    /// next frame. If the cursor is pointing to the back of the list then it
    /// is moved to the "ghost" non-element.
    pub fn take_current(&mut self,
        Tracked(list_perm): Tracked<&mut PointsTo<LinkedList>>,
        Tracked(cur_perm): Tracked<&mut PointsTo<Link>>,
        Tracked(prev_perm): Tracked<&mut PointsTo<Link>>,
        Tracked(next_perm): Tracked<&mut PointsTo<Link>>,
    ) -> Option<UniqueFrameLink> {
        let current = self.current?;

        let mut frame = {
            let meta_ptr = current.borrow(Tracked(&*cur_perm)).meta.to_vaddr();
            let paddr = mapping::meta_to_frame::<PagingConsts>(meta_ptr as Vaddr);
            // SAFETY: The frame was forgotten when inserted into the linked list.
            unsafe { UniqueFrameLink::from_raw(paddr) }
        };

        let mut frame_meta_mut = frame.meta_mut().take(Tracked(cur_perm));

        let next_ptr = frame.meta().next;

        if let Some(prev) = frame_meta_mut.prev {
            // SAFETY: We own the previous node by `&mut self` and the node is
            // initialized.
            let mut prev_mut = prev.take(Tracked(prev_perm));
            prev_mut.next = next_ptr;
            prev.put(Tracked(prev_perm), prev_mut);
        } else {
            let mut list_mut = self.list.take(Tracked(list_perm));
            list_mut.front = next_ptr;
            self.list.put(Tracked(list_perm), list_mut);
        }
        let prev_ptr = frame.meta().prev;
        if let Some(next) = frame_meta_mut.next {
            // SAFETY: We own the next node by `&mut self` and the node is
            // initialized.
            let mut next_mut = next.take(Tracked(prev_perm));
            next_mut.prev = prev_ptr;
            next.put(Tracked(next_perm), next_mut);

            self.current = Some(next);
        } else {
            let mut list_mut = self.list.take(Tracked(list_perm));
            list_mut.back = prev_ptr;
            self.list.put(Tracked(list_perm), list_mut);
            self.current = None;
        }

        frame_meta_mut.next = None;
        frame_meta_mut.prev = None;
        frame.meta_mut().put(Tracked(cur_perm), frame_meta_mut);

//        frame.slot().in_list.store(0, Ordering::Relaxed);
//        frame.slot().in_list_store(0);

        let mut list_mut = self.list.take(Tracked(list_perm));
        list_mut.size = list_mut.size - 1;
        self.list.put(Tracked(list_perm), list_mut);

        Some(frame)
    }

    /// Inserts a frame before the current frame.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new
    /// element is inserted at the back of the [`LinkedList`].
    pub fn insert_before(&mut self, mut frame: UniqueFrameLink,
        Tracked(list_perm): Tracked<&mut PointsTo<LinkedList>>,
        Tracked(frame_perm): Tracked<&mut PointsTo<Link>>,
        Tracked(cur_perm): Tracked<&mut PointsTo<Link>>,
        Tracked(prev_perm): Tracked<&mut PointsTo<Link>>,
        Tracked(next_perm): Tracked<&mut PointsTo<Link>>,
        Tracked(back_perm): Tracked<&mut PointsTo<Link>>,
    ) {
        // The frame can't possibly be in any linked lists since the list will
        // own the frame so there can't be any unique pointers to it.
//        debug_assert!(frame.meta_mut().next.is_none());
//        debug_assert!(frame.meta_mut().prev.is_none());
//        debug_assert_eq!(frame.slot().in_list.load(Ordering::Relaxed), 0);

        let frame_ptr = frame.meta_mut();
        let mut frame_meta_mut = frame_ptr.take(Tracked(frame_perm));

        if let Some(current) = self.current {
            // SAFETY: We own the current node by `&mut self` and the node is
            // initialized.
            let mut current_mut = current.take(Tracked(cur_perm));

            if let Some(prev) = current_mut.prev {
                // SAFETY: We own the previous node by `&mut self` and the node
                // is initialized.
                let mut prev_mut = prev.take(Tracked(prev_perm));

//                debug_assert_eq!(prev_mut.next, Some(*current));
                prev_mut.next = Some(frame_ptr);
                prev.put(Tracked(prev_perm), prev_mut);

                frame_meta_mut.prev = Some(prev);
                frame_meta_mut.next = Some(current);
                current_mut.prev = Some(frame_ptr);
            } else {
//                debug_assert_eq!(self.list.front, Some(*current));
                frame_meta_mut.next = Some(current);
                current_mut.prev = Some(frame_ptr);
                
                let mut list_mut = self.list.take(Tracked(list_perm));
                list_mut.front = Some(frame_ptr);
                self.list.put(Tracked(list_perm), list_mut);
            }
        } else {
            // We are at the "ghost" non-element.
            let mut list_mut = self.list.take(Tracked(list_perm));

            if let Some(back) = list_mut.back {
                // SAFETY: We have ownership of the links via `&mut self`.
//                    debug_assert!(back.as_mut().next.is_none());
                let mut back_mut = back.take(Tracked(back_perm));
                back_mut.next = Some(frame_ptr);
                back.put(Tracked(back_perm), back_mut);

                frame_meta_mut.prev = Some(back);

                list_mut.back = Some(frame_ptr);
            } else {
//                debug_assert_eq!(self.list.front, None);
                list_mut.front = Some(frame_ptr);
                list_mut.back = Some(frame_ptr);
            }

            self.list.put(Tracked(list_perm), list_mut);
        }

        frame_ptr.put(Tracked(frame_perm), frame_meta_mut);

        /*
        frame
            .slot()
            .in_list
            .store(self.list.lazy_get_id(), Ordering::Relaxed);
        */

//        frame.slot().in_list_store(self.list.borrow(Tracked(&*list_perm)).lazy_get_id());


        // Forget the frame to transfer the ownership to the list.
        let _ = frame.into_raw();

        let mut list_mut = self.list.take(Tracked(list_perm));
        list_mut.size = list_mut.size + 1;
        self.list.put(Tracked(list_perm), list_mut);
    }

/*    /// Provides a reference to the linked list.
    pub fn as_list(&self, Tracked(list_perm): Tracked<&mut PointsTo<LinkedList>>) -> &LinkedList {
        self.list.borrow(Tracked(list_perm))
    }*/
}

/*impl Drop for LinkedList
{
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    fn drop(&mut self) {
        unimplemented!()
//        let mut cursor = self.cursor_front_mut();
//        while cursor.take_current().is_some() {}
    }
}*/
/*
impl Deref for Link {
    type Target = FrameMeta;

    #[rustc_allow_incoherent_impl]
    fn deref(&self) -> &Self::Target {
        &self.meta
    }
}

impl DerefMut for Link {
    #[rustc_allow_incoherent_impl]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.meta
    }
}
*/
impl Link {

    #[rustc_allow_incoherent_impl]
    /// Creates a new linked list metadata.
    pub const fn new(meta: FrameMeta) -> Self {
        Self {
            next: None,
            prev: None,
            meta,
        }
    }
}

// SAFETY: If `M::on_drop` reads the page using the provided `VmReader`,
// the safety is upheld by the one who implements `AnyFrameMeta` for `M`.
/*unsafe impl<M> AnyFrameMeta for Link<M>
where
    M: AnyFrameMeta,
{
    fn on_drop(&mut self, reader: &mut crate::mm::VmReader<crate::mm::Infallible>) {
        self.meta.on_drop(reader);
    }

    fn is_untyped(&self) -> bool {
        self.meta.is_untyped()
    }
}
*/
}