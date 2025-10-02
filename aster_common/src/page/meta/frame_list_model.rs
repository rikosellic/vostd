use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::seq_lib::*;
use vstd_extra::ownership::*;
use vstd_extra::cast_ptr::Repr;

use crate::prelude::*;
use crate::prelude::MetaSlotStorage::FrameLink;
use crate::prelude::LinkedList;

verus! {

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> OwnerOf for Link<M> {
    type Owner = MetaSlotOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        true
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> ModelOf for Link<M> { }

pub ghost struct LinkedListModel {
    pub list: Seq<MetaSlotModel>,
}

impl Inv for LinkedListModel {
    open spec fn inv(&self) -> bool { true }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct LinkedListOwner<M: AnyFrameMeta + Repr<MetaSlotInner>> {
    pub list: Seq<MetaSlotOwner>,
    pub perms: Map<int, Tracked<vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, Link<M>>>>,
    pub list_id: u64,
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Inv for LinkedListOwner<M> {
    open spec fn inv(&self) -> bool
    {
        forall |i:int|
            0 <= i < self.list.len() ==>
            self.inv_at(i)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> LinkedListOwner<M> {
    pub open spec fn inv_at(self, i: int) -> bool
    {
        &&& self.perms.contains_key(i)
        &&& self.perms[i]@.addr() == self.list[i].self_addr
        &&& self.perms[i]@.wf()
        &&& FRAME_METADATA_RANGE().start <= self.perms[i]@.addr() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE()
        &&& self.perms[i]@.is_init()
        &&& self.perms[i]@.value().wf(&self.list[i])
        &&& i == 0 <==> self.perms[i]@.mem_contents().value().prev is None
        &&& i == self.list.len() - 1 <==> self.perms[i]@.mem_contents().value().next is None
        &&& 0 < i ==>
            self.perms[i]@.mem_contents().value().prev is Some &&
            self.perms[i]@.mem_contents().value().prev.unwrap() == self.perms[i-1]@.pptr()
        &&& i < self.list.len() - 1 ==>
            self.perms[i]@.mem_contents().value().next is Some &&
            self.perms[i]@.mem_contents().value().next.unwrap() == self.perms[i+1]@.pptr()
        &&& self.list[i].inv()
        &&& self.list[i].in_list@.points_to(self.list_id)
    }

    pub open spec fn view_helper(owners: Seq<MetaSlotOwner>) -> Seq<MetaSlotModel>
        decreases owners.len()
    {
        if owners.len() == 0 {
            Seq::<MetaSlotModel>::empty()
        } else {
            seq![owners[0].view()].add(Self::view_helper(owners.remove(0)))
        }
    }

    pub proof fn view_preserves_len(owners: Seq<MetaSlotOwner>)
        ensures Self::view_helper(owners).len() == owners.len()
        decreases owners.len()
    {
        if owners.len() == 0 {

        } else {
            Self::view_preserves_len(owners.remove(0))
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> InvView for LinkedListOwner<M> {
    type V = LinkedListModel;

    open spec fn view(&self) -> Self::V {
        LinkedListModel {
            list: Self::view_helper(self.list)
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> LinkedListOwner<M> {
/*    pub open spec fn update_prev(links: Seq<LinkOwner<M>>, i: int, prev: Option<PPtr<Link<M>>>) -> Seq<LinkOwner<M>> {
        let link = links[i];
        let new_link = LinkOwner::<M> {
            prev: prev,
            ..link
        };
        links.update(i, new_link)
    }

    pub open spec fn update_next(links: Seq<LinkOwner<M>>, i: int, next: Option<PPtr<Link<M>>>) -> Seq<LinkOwner<M>> {
        let link = links[i];
        let new_link = LinkOwner::<M> {
            next: next,
            ..link
        };
        links.update(i, new_link)
    }*/

    pub open spec fn region_consistency(self, regions:MetaRegionOwners) -> bool {
        forall |i:int|
            0 <= i < self.list.len() ==>
            self.list[i] == regions.slot_owners[frame_to_index(meta_to_frame(self.list[i].self_addr))]
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> OwnerOf for LinkedList<M> {
    type Owner = LinkedListOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==>
            self.front is Some &&
            self.front.unwrap().addr() == owner.list[0].self_addr &&
            owner.perms[0]@.pptr() == self.front.unwrap() &&
            self.back is Some &&
            self.back.unwrap().addr() == owner.list[owner.list.len()-1].self_addr &&
            owner.perms[owner.list.len()-1]@.pptr() == self.back.unwrap()
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> ModelOf for LinkedList<M> { }

#[rustc_has_incoherent_inherent_impls]
pub ghost struct CursorModel {
    pub ghost fore: Seq<MetaSlotModel>,
    pub ghost rear: Seq<MetaSlotModel>,
    pub ghost list_model: LinkedListModel
}

impl Inv for CursorModel {
    open spec fn inv(&self) -> bool { self.list_model.inv() }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorOwner<M: AnyFrameMeta + Repr<MetaSlotInner>> {
    pub list_own: LinkedListOwner<M>,
    pub list_perm: Tracked<PointsTo<LinkedList<M>>>,

    pub index: int,
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Inv for CursorOwner<M> {
    open spec fn inv(&self) -> bool {
        &&& 0 <= self.index <= self.length()
        &&& self.list_own.inv()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> InvView for CursorOwner<M> {
    type V = CursorModel;

    open spec fn view(&self) -> Self::V {
        let list = self.list_own.view();
        CursorModel {
            fore: list.list.take(self.index),
            rear: list.list.skip(self.index),
            list_model: list,
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> OwnerOf for CursorMut<M> {
    type Owner = CursorOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool
    {
        &&& 0 <= owner.index < owner.length() ==>
            self.current.is_some() &&
            self.current.unwrap().addr() == owner.list_own.list[owner.index].self_addr &&
            owner.list_own.perms[owner.index]@.pptr() == self.current.unwrap()
        &&& owner.index == owner.list_own.list.len() ==>
                self.current.is_none()
        &&& owner.list_perm@.pptr() == self.list
        &&& owner.list_perm@.is_init()
        &&& owner.list_perm@.mem_contents().value().wf(&owner.list_own)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> ModelOf for CursorMut<M> { }

impl CursorModel {
    pub open spec fn current(self) -> Option<MetaSlotModel> {
        if self.rear.len() > 0 {
            Some(self.rear[0])
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> CursorOwner<M> {
    pub open spec fn length(self) -> int {
        self.list_own.list.len() as int
    }

    #[verifier::external_body]
    pub fn list_insert(Tracked(cursor): Tracked<&mut Self>, Tracked(owner): Tracked<&mut MetaSlotOwner>, Tracked(perm): Tracked<&vstd_extra::cast_ptr::PointsTo<MetaSlotStorage, Link<M>>>)
        ensures
            cursor.list_own.list == old(cursor).list_own.list.insert(old(cursor).index, *old(owner)),
            cursor.list_own.list_id == old(cursor).list_own.list_id,
            forall |idx:int| 0 <= idx < cursor.length() ==> cursor.list_own.perms.contains_key(idx),
            forall |idx:int| 0 <= idx < cursor.index ==> cursor.list_own.perms[idx] == old(cursor).list_own.perms[idx],
            forall |idx:int| old(cursor).index < idx <= old(cursor).length() ==> cursor.list_own.perms[idx] == old(cursor).list_own.perms[idx-1],
            cursor.list_own.perms[old(cursor).index]@ == perm,
            cursor.index == old(cursor).index+1,
            cursor.list_perm == old(cursor).list_perm,
            owner == old(owner),
    {
        unimplemented!()
    }

    pub open spec fn front_owner_spec(list_own: LinkedListOwner<M>, list_perm: Tracked<PointsTo<LinkedList<M>>>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: 0,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn front_owner(list_own: LinkedListOwner<M>, list_perm: Tracked<PointsTo<LinkedList<M>>>) -> (res:Self)
        ensures
            res == Self::front_owner_spec(list_own, list_perm)
    {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: 0,
        }
    }

    pub open spec fn back_owner_spec(list_own: LinkedListOwner<M>, list_perm: Tracked<PointsTo<LinkedList<M>>>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: if list_own.list.len() > 0 { list_own.list.len() as int - 1 } else { 0 },
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn back_owner(list_own: LinkedListOwner<M>, list_perm: Tracked<PointsTo<LinkedList<M>>>) -> (res:Self)
        ensures
            res == Self::back_owner_spec(list_own, list_perm)
    {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: if list_own.list.len() > 0 { list_own.list.len() as int - 1 } else { 0 },
        }
    }

    pub open spec fn ghost_owner_spec(list_own: LinkedListOwner<M>, list_perm: Tracked<PointsTo<LinkedList<M>>>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: list_own.list.len() as int,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn ghost_owner(list_own: LinkedListOwner<M>, list_perm: Tracked<PointsTo<LinkedList<M>>>) -> (res:Self)
        ensures
            res == Self::ghost_owner_spec(list_own, list_perm)
    {
        CursorOwner::<M> {
            list_own: list_own,
            list_perm: list_perm,
            index: list_own.list.len() as int,
        }
    }


}

}