// SPDX-License-Identifier: MPL-2.0

//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.

use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::seq_lib::*;
use vstd::atomic::PermissionU64;

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
use vstd_extra::ownership::*;

use aster_common::prelude::*;
use aster_common::prelude::frame_list_model::*;

use ostd_specs::*;

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

impl<M: AnyFrameMeta> LinkedList<M>
{

    /// Gets the number of frames in the linked list.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<LinkedListOwner<M>>
    )]
    pub fn size(&self) -> (s:usize)
        requires
            self.wf(&owner),
            owner.inv()
        ensures
            s == self.model(&owner).list.len()
    {
        proof { LinkedListOwner::view_preserves_len(owner.list); }
        self.size
    }

    /// Tells if the linked list is empty.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<LinkedListOwner<M>>
    )]
    pub fn is_empty(&self) -> (b:bool)
        requires
            self.wf(&owner),
            owner.inv()
        ensures
            b ==> self.size == 0 &&
                self.front is None &&
                self.back is None,
            !b ==> self.size > 0 &&
                self.front is Some &&
                self.back is Some
    {
        let is_empty = self.size == 0;
        is_empty
    }

    /// Pushes a frame to the front of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn push_front(&mut self, frame: UniqueFrame<Link<M>>) {
        self.cursor_front_mut().insert_before(frame);
    }

    /// Pops a frame from the front of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn pop_front(&mut self) -> Option<UniqueFrame<Link<M>>> {
        unimplemented!()
//        self.cursor_front_mut().take_current()
    }

    /// Pushes a frame to the back of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn push_back(&mut self, frame: UniqueFrame<Link<M>>) {
        unimplemented!()
//        self.cursor_at_ghost_mut().insert_before(frame);
    }

    /// Pops a frame from the back of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn pop_back(&mut self) -> Option<UniqueFrame<Link<M>>> {
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
    pub fn cursor_mut_at(&mut self, frame: Paddr) -> Option<CursorMut<M>> {
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
    pub fn cursor_front_mut(&mut self) -> CursorMut<M> {
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
    pub fn cursor_back_mut(&mut self) -> CursorMut<M> {
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
    fn cursor_at_ghost_mut(&mut self) -> CursorMut<M> {
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

impl<M: AnyFrameMeta> CursorMut<M>
{
    /// Moves the cursor to the next frame towards the back.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the first element of the [`LinkedList`]. If it is pointing
    /// to the last element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner<M>>
    )]
    pub fn move_next(&mut self)
        requires
            owner.inv(),
            old(self).wf(&owner),
        ensures
            self.model(&owner.move_next_owner_spec()) == old(self).model(&owner).move_next_spec(),
            owner.move_next_owner_spec().inv(),
            self.wf(&owner.move_next_owner_spec()),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
            }
        }

        proof {
            if self.current is Some {
                assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => borrow_field!(& current => next, owner.list_own.list.tracked_borrow(owner.index).self_perm.borrow()),
            None => borrow_field!(& self.list => front, owner.list_own.self_perm.borrow()),
        };

        proof {
            LinkedListOwner::view_preserves_len(owner.list_own.list);
            assert(self.model(&owner.move_next_owner_spec()).fore == old_self.model(&owner).move_next_spec().fore);
            assert(self.model(&owner.move_next_owner_spec()).rear == old_self.model(&owner).move_next_spec().rear);
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
        with Tracked(owner): Tracked<CursorOwner<M>>
    )]
    pub fn move_prev(&mut self)
        requires
            owner.inv(),
            old(self).wf(&owner),
        ensures
            self.model(&owner.move_prev_owner_spec()) == old(self).model(&owner).move_prev_spec(),
            owner.move_prev_owner_spec().inv(),
            self.wf(&owner.move_prev_owner_spec()),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => borrow_field!(& current => prev, owner.list_own.list.tracked_borrow(owner.index).self_perm.borrow()),
            None => borrow_field!(& self.list => back, owner.list_own.self_perm.borrow()),
        };

        proof {
            LinkedListOwner::view_preserves_len(owner.list_own.list);

            if owner@.list_model.list.len() > 0 {
                if owner@.fore.len() > 0 {
                    assert(self.model(&owner.move_prev_owner_spec()).fore == old_self.model(&owner).move_prev_spec().fore);
                    assert(self.model(&owner.move_prev_owner_spec()).rear == old_self.model(&owner).move_prev_spec().rear);
                    if owner@.rear.len() > 0 {
                        assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
                    }
                } else {
                    assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
                    assert(self.model(&owner.move_prev_owner_spec()).rear == old_self.model(&owner).move_prev_spec().rear);
                    assert(owner@.rear == owner@.list_model.list);
                }
            }
        }
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
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(region) : Tracked<MetaRegionOwners>,
            Tracked(owner) : Tracked<&mut CursorOwner<M>>,
            Tracked(frame_owner) : Tracked<UniqueFrameLinkOwner<M>>
    )]
    pub fn take_current(&mut self) -> (res: Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameLinkOwner<M>>)>)
        requires
            FRAME_METADATA_RANGE().start <= old(self).current.unwrap().addr() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE(),
            old(self).current.unwrap().addr() % META_SLOT_SIZE() == 0,
            old(self).wf(old(owner)),
            old(owner).inv(),
            old(self).current.is_some(),
            frame_owner == UniqueFrameLinkOwner::<M>::from_raw_owner(region, old(self).current.unwrap().addr()),
        ensures
            res.is_some() ==> res.unwrap().0.model(&res.unwrap().1@).slot == old(owner).view().current().unwrap().slot,
            res.is_some() ==> self.model(&*owner) == old(self).model(&old(owner)).remove(),
    {
        let ghost owner0 = *owner;

        let current = self.current?;

        assert(owner.length > 0);
        assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
        assert(owner.index > 0 ==> LinkedListOwner::inv_at(owner.list_own.list, owner.index-1, owner.list_own.list_id));
        assert(owner.index < owner.length - 1 ==> LinkedListOwner::inv_at(owner.list_own.list, owner.index+1, owner.list_own.list_id));

        let meta_ptr = current.addr();
        let paddr = mapping::meta_to_frame(meta_ptr);

        #[verus_spec(with Tracked(region))]
        let mut frame = UniqueFrame::<Link<M>>::from_raw(paddr);
        assert(frame.model(&frame_owner).slot == owner@.current().unwrap().slot) by { admit() };

        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);
        let ghost cur_own_old = cur_own;
        let next_ptr = frame.meta(Tracked(cur_own.self_perm.borrow())).next;
        let opt_prev = borrow_field!(&mut frame.meta_mut(Tracked(cur_own.self_perm.borrow_mut())) => prev, cur_own.self_perm.borrow_mut());
        assert(cur_own_old == cur_own) by { admit() };
        proof { owner.list_own.list.tracked_insert(owner.index, cur_own); }

        if let Some(prev) = opt_prev {
            // SAFETY: We own the previous node by `&mut self` and the node is
            // initialized.

            let tracked mut prev_own = owner.list_own.list.tracked_remove(owner.index-1);
            update_field!(prev => next <- next_ptr; prev_own.self_perm);
            proof {
                prev_own.next = next_ptr;
                owner.list_own.list.tracked_insert(owner.index-1, prev_own);
                LinkedListOwner::view_preserves_len(owner.list_own.list);
            }

            assert(forall |i:int| 0 <= i < owner.index ==> owner@.fore[i] == owner.list_own.list[i]@) by { admit() };
            assert(forall |i:int| 0 <= i < owner.index ==> owner0@.fore[i] == owner0.list_own.list[i]@) by { admit() };
            assert(owner@.fore == owner0@.fore.update(owner.index-1, prev_own@)) by { admit() };
            assert(owner@.fore == LinkedListModel::update_next(owner0@.fore, owner.index-1, cur_own@.next));

        } else {
            update_field!(self.list => front <- next_ptr; owner.list_own.self_perm);
        }

        assert(owner@.fore == if owner.index > 0 { LinkedListModel::update_next(owner0@.fore, owner.index-1, cur_own@.next) }
                                            else { owner0@.fore });

        let ghost owner1 = *owner;

        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);
        let ghost cur_own_old = cur_own;
        let prev_ptr = frame.meta(Tracked(cur_own.self_perm.borrow())).prev;
        let opt_next = borrow_field!(&mut frame.meta_mut(Tracked(cur_own.self_perm.borrow_mut())) => next, cur_own.self_perm.borrow_mut()) ;
        assert(cur_own_old == cur_own) by { admit() };
        proof { owner.list_own.list.tracked_insert(owner.index, cur_own); }

        assert(owner1@ == owner@) by { admit()};
        let ghost owner2 = *owner;

        if let Some(next) = opt_next {
            // SAFETY: We own the next node by `&mut self` and the node is
            // initialized.

            let tracked mut next_own = owner.list_own.list.tracked_remove(owner.index+1);
            update_field!(next => prev <- prev_ptr; next_own.self_perm);
            proof {
                next_own.prev = prev_ptr;
                owner.list_own.list.tracked_insert(owner.index+1, next_own);
//                LinkedListOwner::view_preserves_len(owner.list_own.list);
            }

            assert(
                next_own@ == LinkModel::<M> {
                    prev: prev_ptr,
                    ..next_own@
                }
            );

            assert(forall |i:int|
                0 <= i <= owner.index ==>
                #[trigger] owner.list_own.list[i] == owner2.list_own.list[i]);

            assert(forall |i:int|
                0 <= i <= owner.index ==>
                #[trigger] owner@.list_model.list[i] == owner2@.list_model.list[i]) by { admit() };

            assert(owner@.fore == owner@.list_model.list.take(owner.index));
            assert(owner2@.fore == owner2@.list_model.list.take(owner.index));
            assert(owner@.fore == owner2@.fore) by { admit() };

            assert(owner.list_own.list[owner.index+1]@ == next_own@);

            assert(forall |i:int|
                    owner.index <= i < owner.length ==>
                    owner@.rear[i-owner.index] == owner.list_own.list[i]@) by { admit() };

            assert(forall |i:int|
                    owner2.index <= i < owner.length ==>
                    owner2@.rear[i-owner.index] == owner2.list_own.list[i]@) by { admit() };

            assert(owner.list_own.list[owner.index] == owner2.list_own.list[owner.index]);
            assert(owner@.rear[0] == owner2@.rear[0]);

            assert(forall |i:int|
                i > 1 ==>
                owner.index+i < owner.length ==>
                #[trigger] owner.list_own.list[owner.index+i] == owner2.list_own.list[owner.index+i]);

            assert(owner@.rear == owner2@.rear.update(1, next_own@)) by { admit() };

/*            assert(forall |i:int|
                0 <= i < owner@.rear.len() ==>
                i != 1 ==>
                owner@.rear[i] == owner1@.rear[i]);*/

            assert(owner@.rear == LinkedListModel::update_prev(owner2@.rear, 1, cur_own@.prev));

            self.current = Some(next);
        } else {
            assert(owner.remaining <= 1);
            update_field!(self.list => back <- prev_ptr; owner.list_own.self_perm);
            self.current = None;
        }

        assert(owner@.rear == if owner.remaining > 1 { LinkedListModel::update_prev(owner2@.rear, 1, cur_own@.prev) }
                                            else { owner2@.rear });

        let ghost owner3 = *owner;
        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);
        assert(owner@.rear == owner3@.rear.remove(0)) by { admit() };
        let ghost owner4 = *owner;

        update_field!(frame.meta_mut(Tracked(cur_own.self_perm.borrow_mut())) => next <- None; cur_own.self_perm);
        update_field!(frame.meta_mut(Tracked(cur_own.self_perm.borrow_mut())) => prev <- None; cur_own.self_perm);

//        frame.slot().in_list.store(0, Ordering::Relaxed);
//        frame.slot().in_list_store(0);

        update_field!(self.list => size -= 1; owner.list_own.self_perm);

        assert(owner@ == owner4@);

        assert(frame.model(&frame_owner).slot == owner1.view().current().unwrap().slot) by { admit() };

//        assert(owner@.fore == old_owner@.remove().fore);

        assert(self.model(&*owner) == old(self).model(&owner0).remove()) by { admit() };

        Some((frame, Tracked(frame_owner)))
    }

    /// Inserts a frame before the current frame.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new
    /// element is inserted at the back of the [`LinkedList`].
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameLinkOwner<M>>,
            Tracked(in_list_perm): Tracked<&mut PermissionU64>
    )]
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf(old(owner)),
            old(owner).inv(),
            frame.wf(old(frame_own)),
            old(frame_own).inv(),
            old(owner).length < usize::MAX,
/*        ensures
            *owner == old(owner).insert_owner_spec(frame_own.link_own),
            self.model(owner) == old(self).model(old(owner)).insert(frame.model(frame_own)),
            self.wf(&*owner),
            owner.inv(),*/
    {
        // The frame can't possibly be in any linked lists since the list will
        // own the frame so there can't be any unique pointers to it.
//        debug_assert!(frame.meta_mut().next.is_none());
//        debug_assert!(frame.meta_mut().prev.is_none());
//        debug_assert_eq!(frame.slot().in_list.load(Ordering::Relaxed), 0);

        let frame_ptr = frame.meta_mut(Tracked(frame_own.link_own.self_perm.borrow_mut()));

        if let Some(current) = borrow_field!(&mut self.current) {
            assert(LinkedListOwner::inv_at(owner.list_own.list, owner.index, owner.list_own.list_id));
            assert(owner.index > 0 ==> LinkedListOwner::inv_at(owner.list_own.list, owner.index-1, owner.list_own.list_id));
            assert(owner.index < owner.length - 1 ==> LinkedListOwner::inv_at(owner.list_own.list, owner.index+1, owner.list_own.list_id));

            // SAFETY: We own the current node by `&mut self` and the node is
            // initialized.
            let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);
            let opt_prev = borrow_field!(& current => prev, cur_own.self_perm.borrow());
            proof { owner.list_own.list.tracked_insert(owner.index, cur_own); }
            
            if let Some(prev) = opt_prev {
                // SAFETY: We own the previous node by `&mut self` and the node
                // is initialized.
                update_field!(prev => next <- Some(frame_ptr); owner.list_own.list, owner.index-1);
                update_field!(frame_ptr => prev <- Some(prev); frame_own.link_own.self_perm);
                update_field!(frame_ptr => next <- Some(current); frame_own.link_own.self_perm);
                update_field!(current => prev <- Some(frame_ptr); owner.list_own.list, owner.index);
            } else {
                update_field!(frame_ptr => next <- Some(current); frame_own.link_own.self_perm);
                update_field!(current => prev <- Some(frame_ptr); owner.list_own.list, owner.index);
                
                update_field!(self.list => front <- Some(frame_ptr); owner.list_own.self_perm);
            }
        } else {
            assert(0 < owner.length ==> LinkedListOwner::inv_at(owner.list_own.list, owner.length-1, owner.list_own.list_id));

            // We are at the "ghost" non-element.
            if let Some(back) = borrow_field!(&mut self.list => back, owner.list_own.self_perm.borrow_mut()) {
                // SAFETY: We have ownership of the links via `&mut self`.
//                    debug_assert!(back.as_mut().next.is_none());
                update_field!(back => next <- Some(frame_ptr); owner.list_own.list, owner.length-1);
                update_field!(frame_ptr => prev <- Some(back); frame_own.link_own.self_perm);
                update_field!(self.list => back <- Some(frame_ptr); owner.list_own.self_perm);
            } else {
//                debug_assert_eq!(self.list.front, None);
                update_field!(self.list => front <- Some(frame_ptr); owner.list_own.self_perm);
                update_field!(self.list => back <- Some(frame_ptr); owner.list_own.self_perm);
            }
        }

//        frame
//            .slot()
//            .in_list
//            .store(in_list_perm, borrow_field!(& self.list, owner.list_perm).lazy_get_id());

//        frame.slot().in_list_store(self.list.borrow(Tracked(&*list_perm)).lazy_get_id());


        // Forget the frame to transfer the ownership to the list.
//        let _ = frame.into_raw();

        update_field!(self.list => size += 1; owner.list_own.self_perm);
        
    }

    /// Provides a reference to the linked list.
    #[rustc_allow_incoherent_impl]
    pub fn as_list(&self) -> PPtr<LinkedList<M>> {
        self.list
    }
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
impl<M: AnyFrameMeta> Link<M> {

    #[rustc_allow_incoherent_impl]
    /// Creates a new linked list metadata.
    pub const fn new(meta: M) -> Self {
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