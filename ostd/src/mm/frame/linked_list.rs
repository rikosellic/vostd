// SPDX-License-Identifier: MPL-2.0

//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.

use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::seq_lib::*;

use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

use core::borrow::BorrowMut;

use super::{
    meta::{get_slot},
    MetaSlot,
};

use vstd_extra::{borrow_field, update_field};
use aster_common::prelude::{OwnerOf, ModelOf, Inv, InvView, meta, mapping, Link, LinkedList, CursorMut, UniqueFrameLink, FrameMeta, FRAME_METADATA_RANGE, META_SLOT_SIZE};
use aster_common::prelude::frame_list_model::*;

use crate::{
    arch::mm::PagingConsts,
    mm::{Paddr, Vaddr},
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

// SAFETY: Only the pointers are not `Send` and `Sync`. But our interfaces
// enforces that only with `&mut` references can we access with the pointers.
//unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
//unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}

impl LinkedList
{

    /// Gets the number of frames in the linked list.
    #[rustc_allow_incoherent_impl]
    pub fn size(&self) -> usize {
        self.size
    }

    /// Tells if the linked list is empty.
    #[rustc_allow_incoherent_impl]
    pub fn is_empty(&self) -> bool {
        let is_empty = self.size == 0;
//        debug_assert_eq!(is_empty, self.front.is_none());
//        debug_assert_eq!(is_empty, self.back.is_none());
        is_empty
    }

    /// Pushes a frame to the front of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn push_front(&mut self, frame: UniqueFrameLink) {
        unimplemented!()
//        self.cursor_front_mut().insert_before(frame);
    }

    /// Pops a frame from the front of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn pop_front(&mut self) -> Option<UniqueFrameLink> {
        unimplemented!()
//        self.cursor_front_mut().take_current()
    }

    /// Pushes a frame to the back of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn push_back(&mut self, frame: UniqueFrameLink) {
        unimplemented!()
//        self.cursor_at_ghost_mut().insert_before(frame);
    }

    /// Pops a frame from the back of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn pop_back(&mut self) -> Option<UniqueFrameLink> {
        unimplemented!()
//        self.cursor_back_mut().take_current()
    }

    /// Tells if a frame is in the list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn contains(&mut self, frame: Paddr) -> bool {
        unimplemented!()
/*        let Ok(slot) = get_slot(frame) else {
            return false;
        };
//        slot.in_list.load(Ordering::Relaxed) == self.lazy_get_id()
        slot.in_list_load() == self.lazy_get_id()*/
    }

    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fail if [`Self::contains`] returns `false`.
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
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

    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
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

    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
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

    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
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
    #[rustc_allow_incoherent_impl]
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

impl FrameMeta {
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    pub fn to_vaddr(&self) -> Vaddr {
        unimplemented!()
    }
}

impl CursorMut
{
    /// Moves the cursor to the next frame towards the back.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the first element of the [`LinkedList`]. If it is pointing
    /// to the last element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner>
    )]
    pub fn move_next(&mut self)
        requires
            owner.inv(),
            old(self).wf(&owner),
        ensures
            self.model(&owner.move_next_owner_spec()) == old(self).model(&owner).move_next_spec(),
//            owner.move_next_owner_spec().inv(),
            self.wf(&owner.move_next_owner_spec()),
    {
        let ghost old_self = *self;

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => borrow_field!(current => next, owner.cur_perm.tracked_unwrap().borrow()),
            None => borrow_field!(self.list => front, owner.list_perm.borrow()),
        };

        proof {
            LinkedListOwner::view_preserves_len(owner.list_own.list);
            assert(self.model(&owner.move_next_owner_spec()).fore == old_self.model(&owner).move_next_spec().fore);
            assert(self.model(&owner.move_next_owner_spec()).rear == old_self.model(&owner).move_next_spec().rear);

            if owner.cur_perm.is_some() {
                assert(owner.move_next_owner_spec().cur_perm == owner.next_perm);
                assert(owner.next_perm == owner.list_own.list[owner.index].next_perm);
                if owner.next_perm.is_some() {
                    assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index));
                    assert(owner.remaining > 1) by { admit() };
                } else {
                    assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index));
                    assert(self.current.is_none());
                    assert(owner.remaining == 1) by { admit() };
                }
//                assert(owner.list_own.list[owner.index].next_perm);
            } else {
                admit()
            }
        }
    }

    /// Moves the cursor to the previous frame towards the front.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the last element of the [`LinkedList`]. If it is pointing
    /// to the first element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner>
    )]
    pub fn move_prev(&mut self)
        requires
            owner.inv(),
            old(self).wf(&owner),
        ensures
            self.model(&owner) == old(self).model(&owner).move_prev_spec()
    {
        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => borrow_field!(current => prev, owner.cur_perm.tracked_unwrap().borrow()),
            None => borrow_field!(self.list => front, owner.list_perm.borrow()),
        };
    }

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
/*    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut CursorOwner>
    )]
    pub fn take_current(&mut self) -> (res: Option<UniqueFrameLink>)
    {
        let current = self.current?;

        let mut frame = {
            let meta_ptr = current.addr();
            assert(FRAME_METADATA_RANGE().start <= meta_ptr < FRAME_METADATA_RANGE().end) by { admit() };
            assert(meta_ptr % META_SLOT_SIZE() == 0) by { admit() };

            let paddr = mapping::meta_to_frame(meta_ptr);
            // SAFETY: The frame was forgotten when inserted into the linked list.
            unsafe { UniqueFrameLink::from_raw(paddr) }
        };

        let next_ptr = frame.meta(Tracked(owner.cur_perm.borrow())).next;

        if let Some(prev) = frame.meta_mut(Tracked(owner.cur_perm.borrow_mut())).borrow(Tracked(owner.cur_perm.borrow())).prev {
            // SAFETY: We own the previous node by `&mut self` and the node is
            // initialized.

            update_field!(prev => next <- next_ptr, owner.prev_perm.borrow_mut());
        } else {
            update_field!(self.list => front <- next_ptr, owner.list_perm.borrow_mut());
        }
        let prev_ptr = frame.meta(Tracked(owner.cur_perm.borrow())).prev;
        if let Some(next) = frame.meta_mut(Tracked(owner.cur_perm.borrow_mut())).borrow(Tracked(owner.cur_perm.borrow())).next {
            // SAFETY: We own the next node by `&mut self` and the node is
            // initialized.

            update_field!(next => prev <- prev_ptr, owner.next_perm.borrow_mut());
            self.current = Some(next);
        } else {
            update_field!(self.list => back <- prev_ptr, owner.list_perm.borrow_mut());
            self.current = None;
        }

        update_field!(frame.meta_mut(Tracked(owner.cur_perm.borrow_mut())) => next <- None, owner.cur_perm.borrow_mut());
        update_field!(frame.meta_mut(Tracked(owner.cur_perm.borrow_mut())) => prev <- None, owner.cur_perm.borrow_mut());

//        frame.slot().in_list.store(0, Ordering::Relaxed);
//        frame.slot().in_list_store(0);

        update_field!(self.list => size -= 1, owner.list_perm.borrow_mut());

        Some(frame)
    }*/

    /// Inserts a frame before the current frame.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new
    /// element is inserted at the back of the [`LinkedList`].
    #[rustc_allow_incoherent_impl]
    pub fn insert_before(&mut self, mut frame: UniqueFrameLink,
            Tracked(list_perm): Tracked<&mut PointsTo<LinkedList>>,
            Tracked(frame_perm): Tracked<&mut PointsTo<Link>>,
            Tracked(cur_perm): Tracked<&mut PointsTo<Link>>,
            Tracked(prev_perm): Tracked<&mut PointsTo<Link>>,
            Tracked(next_perm): Tracked<&mut PointsTo<Link>>,
            Tracked(back_perm): Tracked<&mut PointsTo<Link>>,
            link_model: Ghost<LinkModel>,
            cursor_model: Ghost<CursorModel>)
//            -> (res: Ghost<LinkedListModel>)
        requires
            old(self).list == old(list_perm).pptr(),
            old(list_perm).is_init(),
            old(list_perm).mem_contents().value().size < usize::MAX,
            old(list_perm).mem_contents().value().back.unwrap() == old(back_perm).pptr(),
            old(self).current.unwrap() == old(cur_perm).pptr(),
            old(cur_perm).is_init(),
            old(cur_perm).mem_contents().value().prev == Some(old(prev_perm).pptr()),
            old(cur_perm).mem_contents().value().next == Some(old(next_perm).pptr()),
            old(back_perm).is_init(),
            old(frame_perm).is_init(),
            old(prev_perm).is_init(),
    {
        // The frame can't possibly be in any linked lists since the list will
        // own the frame so there can't be any unique pointers to it.
//        debug_assert!(frame.meta_mut().next.is_none());
//        debug_assert!(frame.meta_mut().prev.is_none());
//        debug_assert_eq!(frame.slot().in_list.load(Ordering::Relaxed), 0);

        let frame_ptr = frame.meta_mut(Tracked(frame_perm));

        if let Some(current) = self.current {
            // SAFETY: We own the current node by `&mut self` and the node is
            // initialized.

            if let Some(prev) = borrow_field!(current => prev, &*cur_perm) {
                // SAFETY: We own the previous node by `&mut self` and the node
                // is initialized.
                update_field!(prev => next <- Some(frame_ptr), prev_perm);
                update_field!(frame_ptr => prev <- Some(prev), frame_perm);
                update_field!(frame_ptr => next <- Some(current), frame_perm);
                update_field!(current => prev <- Some(frame_ptr), cur_perm);
            } else {
                update_field!(frame_ptr => next <- Some(current), frame_perm);
                update_field!(current => prev <- Some(frame_ptr), cur_perm);
                
                update_field!(self.list => front <- Some(frame_ptr), list_perm);
            }
        } else {
            // We are at the "ghost" non-element.
            if let Some(back) = self.list.borrow(Tracked(&*list_perm)).back {
                // SAFETY: We have ownership of the links via `&mut self`.
//                    debug_assert!(back.as_mut().next.is_none());
                update_field!(back => next <- Some(frame_ptr), back_perm);
                update_field!(frame_ptr => prev <- Some(back), frame_perm);
                update_field!(self.list => back <- Some(frame_ptr), list_perm);
            } else {
//                debug_assert_eq!(self.list.front, None);
                update_field!(self.list => front <- Some(frame_ptr), list_perm);
                update_field!(self.list => back <- Some(frame_ptr), list_perm);
            }
        }

        /*
        frame
            .slot()
            .in_list
            .store(self.list.lazy_get_id(), Ordering::Relaxed);
        */

//        frame.slot().in_list_store(self.list.borrow(Tracked(&*list_perm)).lazy_get_id());


        // Forget the frame to transfer the ownership to the list.
//        let _ = frame.into_raw();

        update_field!(self.list => size += 1, list_perm);

//        let ghost (cursor_model, list_model) = cursor_model@.remove(list_model@);
//        Ghost(list_model)
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
//            meta,
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