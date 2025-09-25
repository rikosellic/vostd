// SPDX-License-Identifier: MPL-2.0

//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.

use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::seq_lib::*;
use vstd::atomic::PermissionU64;

use verus_builtin::tracked_exec;

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
use vstd_extra::cast_ptr::*;

use aster_common::prelude::*;
use aster_common::prelude::frame_list_model::*;

use ostd_specs::*;

use crate::{
    mm::{Paddr, Vaddr},
};

verus! {

// SAFETY: Only the pointers are not `Send` and `Sync`. But our interfaces
// enforces that only with `&mut` references can we access with the pointers.
//unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
//unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> LinkedList<M>
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
        proof { LinkedListOwner::<M>::view_preserves_len(owner.list); }
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
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameLinkOwner<M>>
    )]
    pub fn push_front(ptr: PPtr<Self>, frame: UniqueFrame<Link<M>>)
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(&owner),
            owner.inv(),
            owner.list_id != 0,
            old(frame_own).inv(),
            frame.wf(old(frame_own)),
            owner.list.len() < usize::MAX,
            old(regions).slots.contains_key(frame_to_index(frame.ptr.addr())),
            old(regions).slots[frame_to_index(frame.ptr.addr())]@.is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame.ptr.addr())),
            old(regions).slot_owners[frame_to_index(frame.ptr.addr())].in_list@.is_for(
                old(regions).slots[frame_to_index(frame.ptr.addr())]@.mem_contents().value().in_list),
    {
        #[verus_spec(with Tracked(owner), Tracked(perm))]
        let (cursor, cursor_own) = Self::cursor_front_mut(ptr);
        let mut cursor = cursor;
        let tracked mut cursor_own = cursor_own;

        #[verus_spec(with Tracked(regions), Tracked(cursor_own.borrow_mut()), Tracked(frame_own))]
        cursor.insert_before(frame);
    }

    /// Pops a frame from the front of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameLinkOwner<M>>
    )]
    pub fn pop_front(ptr: PPtr<Self>) -> Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameLinkOwner<M>>)>
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(&owner),
            owner.inv(),
            owner.region_consistency(*old(regions))
    {
        assert(owner.list.len() > 0 ==> owner.inv_at(0));

        #[verus_spec(with Tracked(owner), Tracked(perm))]
        let (cursor, cursor_own) = Self::cursor_front_mut(ptr);
        let mut cursor = cursor;
        let tracked mut cursor_own = cursor_own;

        assert(frame_own == UniqueFrameLinkOwner::<M>::from_raw_owner(*regions, cursor.current.unwrap().addr())) by { admit() };
        
        assert(cursor_own@.length() > 0 ==> cursor.current.unwrap().addr() % META_SLOT_SIZE() == 0) by { admit() };

        #[verus_spec(with Tracked(regions), Tracked(cursor_own.borrow_mut()))]
        cursor.take_current()
    }

    /// Pushes a frame to the back of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameLinkOwner<M>>
    )]
    pub fn push_back(ptr: PPtr<Self>, frame: UniqueFrame<Link<M>>)
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(&owner),
            owner.inv(),
            owner.list_id != 0,
            old(frame_own).inv(),
            frame.wf(old(frame_own)),
            owner.list.len() < usize::MAX,
            old(regions).slots.contains_key(frame_to_index(frame.ptr.addr())),
            old(regions).slots[frame_to_index(frame.ptr.addr())]@.is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame.ptr.addr())),
            old(regions).slot_owners[frame_to_index(frame.ptr.addr())].in_list@.is_for(
                old(regions).slots[frame_to_index(frame.ptr.addr())]@.mem_contents().value().in_list),
    {
        #[verus_spec(with Tracked(owner), Tracked(perm))]
        let (cursor, cursor_own) = Self::cursor_back_mut(ptr);
        let mut cursor = cursor;
        let tracked mut cursor_own = cursor_own;

        #[verus_spec(with Tracked(regions), Tracked(cursor_own.borrow_mut()), Tracked(frame_own))]
        cursor.insert_before(frame);
    }

    /// Pops a frame from the back of the linked list.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameLinkOwner<M>>
    )]
    pub fn pop_back(ptr: PPtr<Self>) -> Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameLinkOwner<M>>)>
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(&owner),
            owner.inv(),
            owner.region_consistency(*old(regions))
    {
        assert(owner.list.len() > 0 ==> owner.inv_at(owner.list.len() - 1));

        #[verus_spec(with Tracked(owner), Tracked(perm))]
        let (cursor, cursor_own) = Self::cursor_back_mut(ptr);
        let mut cursor = cursor;
        let tracked mut cursor_own = cursor_own;

        assert(frame_own == UniqueFrameLinkOwner::<M>::from_raw_owner(*regions, cursor.current.unwrap().addr())) by { admit() };
        
        assert(cursor_own@.length() > 0 ==> cursor.current.unwrap().addr() % META_SLOT_SIZE() == 0) by { admit() };

        #[verus_spec(with Tracked(regions), Tracked(cursor_own.borrow_mut()))]
        cursor.take_current()
    }

    /// Tells if a frame is in the list.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    pub fn contains(ptr: PPtr<Self>, frame: Paddr) -> bool
        requires
            old(regions).inv(),
            old(regions).slots.contains_key(frame_to_index(frame)),
            old(regions).slots[frame_to_index(frame)]@.is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame)),
            old(regions).slot_owners[frame_to_index(frame)].in_list@.is_for(old(regions).slots[frame_to_index(frame)]@.mem_contents().value().in_list),
    {
        let Ok(slot_ptr) = get_slot(frame, Tracked(regions)) else {
            return false;
        };

        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(frame));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));

        let slot = slot_ptr.take(Tracked(slot_perm.borrow_mut()));
        let in_list = slot.in_list.load(Tracked(slot_own.in_list.borrow_mut()));
        slot_ptr.put(Tracked(slot_perm.borrow_mut()), slot);

        proof {
            regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
            regions.slots.tracked_insert(frame_to_index(frame), slot_perm);
        }

        #[verus_spec(with Tracked(owner))]
        let id = Self::lazy_get_id(ptr);
        in_list == id
    }

    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fail if [`Self::contains`] returns `false`.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    pub fn cursor_mut_at(ptr: PPtr<Self>, frame: Paddr) -> Option<CursorMut<M>>
        requires
            old(regions).inv(),
            frame < MAX_PADDR(),
            frame % PAGE_SIZE() == 0,
            old(regions).slots.contains_key(frame_to_index(frame)),
            old(regions).slots[frame_to_index(frame)]@.is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame)),
            old(regions).slot_owners[frame_to_index(frame)].in_list@.is_for(old(regions).slots[frame_to_index(frame)]@.mem_contents().value().in_list),
    {
        let Ok(slot_ptr) = get_slot(frame, Tracked(regions)) else {
            return None;
        };

        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(frame));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));

        let slot = slot_ptr.take(Tracked(slot_perm.borrow_mut()));
        let in_list = slot.in_list.load(Tracked(slot_own.in_list.borrow_mut())); 

        #[verus_spec(with Tracked(owner))]
        let id = Self::lazy_get_id(ptr);
        let contains = in_list == id;

        #[verus_spec(with Tracked(regions), Ghost(frame_to_meta(frame)))]
        let meta_ptr : ReprPtr<MetaSlotStorage, Link<M>> = slot.as_meta_ptr();

        let res = if contains {
            Some(CursorMut {
                list: ptr,
                current: Some(meta_ptr),
            })
        } else {
            None
        };

        slot_ptr.put(Tracked(slot_perm.borrow_mut()), slot);
        proof {
            regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
            regions.slots.tracked_insert(frame_to_index(frame), slot_perm);
        }

        res
    }

    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<LinkedListOwner<M>>,
                    perm: Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>
    )]
    pub fn cursor_front_mut(ptr: PPtr<Self>) -> (res:(CursorMut<M>, Tracked<CursorOwner<M>>))
        requires
            perm@.pptr() == ptr,
            perm@.is_init(),
            perm@.mem_contents().value().wf(&owner),
            owner.inv(),
        ensures
            res.0.wf(&res.1@),
            res.1@.inv(),
            res.1@ == CursorOwner::front_owner_spec(owner, perm),
    {
        let ll = ptr.borrow(Tracked(perm.borrow()));
        let current = ll.front;

        (CursorMut {
            list: ptr,
            current,
        },
        Tracked(CursorOwner::front_owner(owner, perm)))
    }

    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<LinkedListOwner<M>>,
                    perm: Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>
    )]
    pub fn cursor_back_mut(ptr: PPtr<Self>) -> (res: (CursorMut<M>, Tracked<CursorOwner<M>>))
        requires    
            perm@.pptr() == ptr,
            perm@.is_init(),
            perm@.mem_contents().value().wf(&owner),
            owner.inv(),
        ensures
            res.0.wf(&res.1@),
            res.1@.inv(),
            res.1@ == CursorOwner::back_owner_spec(owner, perm),
    {
        let ll = ptr.borrow(Tracked(perm.borrow()));
        let current = ll.back;

        (CursorMut {
            list: ptr,
            current,
        },
        Tracked(CursorOwner::back_owner(owner, perm)))
    }

    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    fn cursor_at_ghost_mut(ptr: PPtr<Self>) -> CursorMut<M>
    {
        CursorMut {
            list: ptr,
            current: None,
        }
    }

    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    fn lazy_get_id(ptr: PPtr<Self>) -> (id:u64)
        ensures
            old(owner).list_id != 0 ==> id == old(owner).list_id && owner == old(owner),
    {
        unimplemented!()
/*        // FIXME: Self-incrementing IDs may overflow, while `core::pin::Pin`
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
        }*/
    }
}

}

verus!{

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> CursorMut<M>
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
                assert(owner.list_own.inv_at(owner.index));
            }
            if owner.index < owner.length() - 1 {
                assert(owner.list_own.inv_at(owner.index+1));
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => current.borrow(Tracked(owner.list_own.perms.tracked_borrow(owner.index).borrow())).next,
            None => self.list.borrow(Tracked(owner.list_perm.borrow())).front,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);
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
                assert(owner.list_own.inv_at(owner.index));
            }
            if 0 < owner.index {
                assert(owner.list_own.inv_at(owner.index-1));
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => current.borrow(Tracked(owner.list_own.perms.tracked_borrow(owner.index).borrow())).prev,
            None => self.list.borrow(Tracked(owner.list_perm.borrow())).back,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);

            if owner@.list_model.list.len() > 0 {
                if owner@.fore.len() > 0 {
                    assert(self.model(&owner.move_prev_owner_spec()).fore == old_self.model(&owner).move_prev_spec().fore);
                    assert(self.model(&owner.move_prev_owner_spec()).rear == old_self.model(&owner).move_prev_spec().rear);
                    if owner@.rear.len() > 0 {
                        assert(owner.list_own.inv_at(owner.index));
                    }
                } else {
                    assert(owner.list_own.inv_at(owner.index));
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
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
            Tracked(owner) : Tracked<&mut CursorOwner<M>>
    )]
    pub fn take_current(&mut self) -> (res: Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameLinkOwner<M>>)>)
        requires
            old(owner).length() > 0 ==> old(self).current.unwrap().addr() % META_SLOT_SIZE() == 0,
            old(self).wf(old(owner)),
            old(owner).inv(),
            old(owner).list_own.region_consistency(*old(regions))
        ensures
            old(owner).length() == 0 ==> res.is_none(),
            res.is_some() ==> res.unwrap().0.model(&res.unwrap().1@).slot == old(owner).current().unwrap().slot@,
            res.is_some() ==> self.model(&*owner) == old(self).model(&old(owner)).remove(),
    {
        let ghost owner0 = *owner;

        let current = self.current?;

        assert(owner.list_own.inv_at(owner.index));
        assert(owner.index > 0 ==> owner.list_own.inv_at(owner.index-1));
        assert(owner.index < owner.length() - 1 ==> owner.list_own.inv_at(owner.index+1));

        let meta_ptr = current.addr();
        let paddr = mapping::meta_to_frame(meta_ptr);

        let tracked Tracked(cur_perm) = owner.list_own.perms.tracked_remove(owner.index);

        #[verus_spec(with Tracked(regions), Tracked(cur_perm))]
        let (frame, frame_own) = UniqueFrame::<Link<M>>::from_raw(paddr);
        let mut frame = frame;
        let mut frame_own = frame_own;

        let next_ptr = frame.meta().next;
        #[verus_spec(with Tracked(regions))]
        let frame_meta = frame.meta_mut();

        assert(frame_meta == frame_own@.link_perm@.pptr()) by { admit() };
        let opt_prev = frame_meta.borrow(Tracked(frame_own.borrow().link_perm.borrow())).prev;

        assert(owner.list_own.list == owner0.list_own.list);

        if let Some(prev) = opt_prev {
            // SAFETY: We own the previous node by `&mut self` and the node is
            // initialized.

            let tracked mut prev_perm = owner.list_own.perms.tracked_remove(owner.index-1);
            let mut __tmp = prev.take(Tracked(prev_perm.borrow_mut()));
            __tmp.next = next_ptr;
            prev.put(Tracked(prev_perm.borrow_mut()), __tmp);
            proof { owner.list_own.perms.tracked_insert(owner.index-1, prev_perm); }

            assert(owner.index > 0);
//            assume(owner.list_own.list == LinkedListOwner::update_next(owner0.list_own.list, owner.index-1, owner0.list_own.list[owner.index].next)); /*** KVerus: Help me prove ***/
        } else {
            let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
            __tmp.front = next_ptr;
            self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);
        }

        let prev_ptr = frame.meta().prev;
        #[verus_spec(with Tracked(regions))]
        let frame_meta = frame.meta_mut();
        assert(frame_meta == frame_own@.link_perm@.pptr()) by { admit() };
        let opt_next = frame_meta.borrow(Tracked(frame_own.borrow().link_perm.borrow())).next;

        if let Some(next) = opt_next {
            // SAFETY: We own the next node by `&mut self` and the node is
            // initialized.
            let tracked mut next_perm = owner.list_own.perms.tracked_remove(owner.index+1);
            let mut __tmp = next.take(Tracked(next_perm.borrow_mut()));
            __tmp.prev = prev_ptr;
            next.put(Tracked(next_perm.borrow_mut()), __tmp);
            proof { owner.list_own.perms.tracked_insert(owner.index+1, next_perm); }

            self.current = Some(next);
        } else {
            let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
            __tmp.back = prev_ptr;
            self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);

            self.current = None;
        }

        #[verus_spec(with Tracked(regions))]
        let frame_meta = frame.meta_mut();
        assert(frame_meta == frame_own@.link_perm@.pptr()) by { admit() };
        let mut __tmp = frame_meta.take(Tracked(frame_own.borrow_mut().link_perm.borrow_mut()));
        __tmp.next = None;
        __tmp.prev = None;
        frame_meta.put(Tracked(frame_own.borrow_mut().link_perm.borrow_mut()), __tmp);

//        frame.slot().in_list.store(0, Ordering::Relaxed);
//        frame.slot().in_list_store(0);

        let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
        __tmp.size = __tmp.size - 1;
        self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);

        assert(owner0.remove_owner_spec(*owner));
        proof { owner0.remove_owner_spec_implies_model_spec(*owner); }

        Some((frame, frame_own))
    }

    /// Inserts a frame before the current frame.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new
    /// element is inserted at the back of the [`LinkedList`].
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut CursorOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameLinkOwner<M>>
    )]
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf(old(owner)),
            old(owner).inv(),
            old(owner).list_own.list_id != 0,
            old(frame_own).inv(),
            frame.wf(&old(frame_own)),
            old(owner).length() < usize::MAX,
            old(regions).slots.contains_key(frame_to_index(frame.ptr.addr())),
            old(regions).slots[frame_to_index(frame.ptr.addr())]@.is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame.ptr.addr())),
            old(regions).slot_owners[frame_to_index(frame.ptr.addr())].in_list@.is_for(
                old(regions).slots[frame_to_index(frame.ptr.addr())]@.mem_contents().value().in_list),
        ensures
            self.model(owner) == old(self).model(old(owner)).insert(frame.model(frame_own)),
            self.wf(&*owner),
            owner.inv(),
    {
        let ghost owner0 = *owner;
        // The frame can't possibly be in any linked lists since the list will
        // own the frame so there can't be any unique pointers to it.

        #[verus_spec(with Tracked(regions))]
        let frame_ptr = frame.meta_mut();
        assert(frame_own.link_perm@.pptr() == frame_ptr) by { admit() };
        assert(frame_own.inv()) by { admit() };

        assert(frame_ptr.addr() == frame_own.link_own.paddr) by { admit() };
        assert(frame_own.link_perm@.mem_contents().value().prev is None) by { admit() };
        assert(frame_own.link_perm@.mem_contents().value().next is None) by { admit() };
        assert(FRAME_METADATA_RANGE().start <= frame_own.link_perm@.addr() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES()*META_SLOT_SIZE()) by { admit() };


        if let Some(current) = self.current {
            assert(owner.list_own.inv_at(owner.index));
            assert(owner.index > 0 ==> owner.list_own.inv_at(owner.index-1));
            assert(owner.index < owner.length() - 1 ==> owner.list_own.inv_at(owner.index+1));

            // SAFETY: We own the current node by `&mut self` and the node is
            // initialized.
            let tracked mut cur_perm = owner.list_own.perms.tracked_remove(owner.index);
            let opt_prev = current.borrow(Tracked(cur_perm.borrow())).prev;
            proof { owner.list_own.perms.tracked_insert(owner.index, cur_perm); }

            if let Some(prev) = opt_prev {
                // SAFETY: We own the previous node by `&mut self` and the node
                // is initialized.

                let tracked mut prev_perm = owner.list_own.perms.tracked_remove(owner.index-1);
                let mut __tmp = prev.take(Tracked(prev_perm.borrow_mut()));
                __tmp.next = Some(frame_ptr);
                prev.put(Tracked(prev_perm.borrow_mut()), __tmp);
                proof { owner.list_own.perms.tracked_insert(owner.index-1, prev_perm); }

                let mut __tmp = frame_ptr.take(Tracked(frame_own.link_perm.borrow_mut()));
                __tmp.prev = Some(prev);
                __tmp.next = Some(current);
                frame_ptr.put(Tracked(frame_own.link_perm.borrow_mut()), __tmp);

                let tracked mut cur_perm = owner.list_own.perms.tracked_remove(owner.index);
                let mut __tmp = current.take(Tracked(cur_perm.borrow_mut()));
                __tmp.prev = Some(frame_ptr);
                current.put(Tracked(cur_perm.borrow_mut()), __tmp);
                proof { owner.list_own.perms.tracked_insert(owner.index, cur_perm); }
            } else {
                let mut __tmp = frame_ptr.take(Tracked(frame_own.link_perm.borrow_mut()));
                __tmp.next = Some(current);
                frame_ptr.put(Tracked(frame_own.link_perm.borrow_mut()), __tmp);

                let tracked mut cur_perm = owner.list_own.perms.tracked_remove(owner.index);
                let mut __tmp = current.take(Tracked(cur_perm.borrow_mut()));
                __tmp.prev = Some(frame_ptr);
                current.put(Tracked(cur_perm.borrow_mut()), __tmp);
                proof { owner.list_own.perms.tracked_insert(owner.index, cur_perm); }
                
                let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
                __tmp.front = Some(frame_ptr);
                self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);
            }
        } else {
            // We are at the "ghost" non-element.

            assert(0 < owner.length() ==> owner.list_own.inv_at(owner.index-1));

            if let Some(back) = self.list.borrow(Tracked(owner.list_perm.borrow_mut())).back {
                assert(owner.index == owner.length());

                // SAFETY: We have ownership of the links via `&mut self`.
//                    debug_assert!(back.as_mut().next.is_none());
                let tracked mut back_perm = owner.list_own.perms.tracked_remove(owner.length()-1);
                let mut __tmp = back.take(Tracked(back_perm.borrow_mut()));
                __tmp.next = Some(frame_ptr);
                back.put(Tracked(back_perm.borrow_mut()), __tmp);
                proof { owner.list_own.perms.tracked_insert(owner.length()-1, back_perm); }

                let mut __tmp = frame_ptr.take(Tracked(frame_own.link_perm.borrow_mut()));
                __tmp.prev = Some(back);
                frame_ptr.put(Tracked(frame_own.link_perm.borrow_mut()), __tmp);

                let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
                __tmp.back = Some(frame_ptr);
                self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);
            } else {
//                debug_assert_eq!(self.list.front, None);
                let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
                __tmp.front = Some(frame_ptr);
                __tmp.back = Some(frame_ptr);
                self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);
            }
        }

        assert(regions.slot_owners.contains_key(frame_to_index(frame.ptr.addr()))) by { admit() };
        let slot = frame.slot();
        
        assert(slot == regions.slots[frame_to_index(frame.ptr.addr())]@.mem_contents().value()) by { admit() };
        assert(regions.slot_owners[frame_to_index(frame.ptr.addr())].in_list@.is_for(
                regions.slots[frame_to_index(frame.ptr.addr())]@.mem_contents().value().in_list)) by { admit() };
        assert(frame.ptr.addr() == frame_ptr.addr()) by { admit() };

        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame.ptr.addr()));

        #[verus_spec(with Tracked(&mut owner.list_own))]
        let id = LinkedList::<M>::lazy_get_id(self.list /*Tracked(owner.list_perm.borrow())*/);
        slot.in_list.store(Tracked(slot_own.in_list.borrow_mut()), id);
        proof { regions.slot_owners.tracked_insert(frame_to_index(frame.ptr.addr()), slot_own) }

        CursorOwner::<M>::list_insert(Tracked(owner), Tracked(&mut frame_own.link_own), Tracked(frame_own.link_perm.borrow()));
        assert(owner.list_own.list[owner.index-1].slot@.in_list == owner.list_own.list_id) by { admit() };

        // Forget the frame to transfer the ownership to the list.
//        let _ = frame.into_raw();

        let mut __tmp = self.list.take(Tracked(owner.list_perm.borrow_mut()));
        __tmp.size = __tmp.size + 1;
        self.list.put(Tracked(owner.list_perm.borrow_mut()), __tmp);

        assert(forall |i:int| 0 <= i < owner.index-2 ==> owner.list_own.list[i] == owner0.list_own.list[i]);
        assert(forall |i:int| 0 <= i < owner.index-2 ==> owner.list_own.perms[i] == owner0.list_own.perms[i]);
        assert(forall |i:int| 0 <= i < owner.index-2 ==> owner.list_own.perms.contains_key(i)) by { admit() };
        assert(forall |i:int| 0 <= i < owner.index-2 ==> owner0.list_own.inv_at(i) ==> owner.list_own.inv_at(i));

        assert(forall |i:int| owner.index+1 <= i < owner.length() ==> owner.list_own.list[i] == owner0.list_own.list[i-1]);
        assert(forall |i:int| owner.index+1 <= i < owner.length() ==> owner.list_own.perms[i] == owner0.list_own.perms[i-1]);
        assert(forall |i:int| owner.index+1 <= i < owner.length() ==> owner.list_own.perms.contains_key(i)) by { admit() };
        assert(forall |i:int| owner.index+1 <= i < owner.length() ==> owner0.list_own.inv_at(i-1) == owner.list_own.inv_at(i));

        proof { owner0.insert_owner_spec_implies_model_spec(frame_own.link_own, *owner); }
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
impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Link<M> {

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