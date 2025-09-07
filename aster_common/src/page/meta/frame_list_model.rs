use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::seq_lib::*;
use vstd_extra::ownership::*;

use crate::prelude::*;
use crate::prelude::MetaSlotStorage::FrameLink;
use crate::prelude::LinkedList;

verus! {

pub ghost struct LinkModel<M: AnyFrameMeta> {
    pub paddr: Paddr,
    pub slot: MetaSlotModel,
    pub prev: Option<PPtr<Link<M>>>,
    pub next: Option<PPtr<Link<M>>>,
}

impl<M: AnyFrameMeta> Inv for LinkModel<M> {
    open spec fn inv(&self) -> bool { true }
}

pub tracked struct LinkOwner<M: AnyFrameMeta> {
    pub paddr: Paddr,
    pub slot: MetaSlotOwner,

    pub prev: Option<PPtr<Link<M>>>,
    pub next: Option<PPtr<Link<M>>>
}

impl<M: AnyFrameMeta> Inv for LinkOwner<M> {
    open spec fn inv(&self) -> bool {
        true
//        self.self_perm@.mem_contents() is Init
    }
}

impl<M: AnyFrameMeta> InvView for LinkOwner<M> {
    type V = LinkModel<M>;

    open spec fn view(&self) -> Self::V {
        LinkModel {
            paddr: self.paddr,
            slot: self.slot.view(),
            prev: self.prev,
            next: self.next,
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta> OwnerOf for Link<M> {
    type Owner = LinkOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
//        &&& owner.self_perm@.mem_contents().value() == self
        &&& owner.next == self.next
        &&& owner.prev == self.prev
    }
}

impl<M: AnyFrameMeta> ModelOf for Link<M> { }

pub tracked struct UniqueFrameLinkOwner<M: AnyFrameMeta> {
    pub link_own : LinkOwner<M>,
    pub link_perm : Tracked<PointsTo<Link<M>>>,
    pub frame_own : UniqueFrameOwner<Link<M>>
}

impl<M: AnyFrameMeta> Inv for UniqueFrameLinkOwner<M> {
    open spec fn inv(&self) -> bool {
        true
//        &&& self.link_own.self_perm@.mem_contents() is Init
//        &&& self.link_own.self_perm@.mem_contents().value() == self.frame_own.data
    }
}

impl<M: AnyFrameMeta> InvView for UniqueFrameLinkOwner<M> {
    type V = LinkModel<M>;

    open spec fn view(&self) -> Self::V {
        self.link_own@
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta> OwnerOf for UniqueFrame<Link<M>> {
    type Owner = UniqueFrameLinkOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& owner.link_perm@.is_init()
        &&& self.ptr == owner.frame_own.slot@.self_ptr@.pptr()
        &&& owner.link_perm@.pptr() == Link::<M>::cast_to_spec(&owner.frame_own@.slot.storage.value())
    }
}

impl<M: AnyFrameMeta> ModelOf for UniqueFrame<Link<M>> { }

impl<M: AnyFrameMeta> UniqueFrameLinkOwner<M> {
    pub closed spec fn from_raw_owner(region: MetaRegionOwners, paddr: Paddr) -> Self;
}

pub ghost struct LinkedListModel<M: AnyFrameMeta> {
    pub list: Seq<LinkModel<M>>,
}

impl<M: AnyFrameMeta> LinkedListModel<M> {
    pub open spec fn front(&self) -> Option<LinkModel<M>> {
        if self.list.len() > 0 {
            Some(self.list[0])
        } else {
            None
        }
    }

    pub open spec fn back(&self) -> Option<LinkModel<M>> {
        if self.list.len() > 0 {
            Some(self.list[self.list.len() - 1])
        } else {
            None
        }
    }

}

impl<M: AnyFrameMeta> Inv for LinkedListModel<M> {
    open spec fn inv(&self) -> bool { true }
}

pub tracked struct LinkedListOwner<M: AnyFrameMeta> {
    pub list: Seq<LinkOwner<M>>,
    pub perms: Map<int, Tracked<PointsTo<Link<M>>>>,
    pub list_id: u64,

    pub self_perm: Tracked<PointsTo<LinkedList<M>>>,
}

impl<M: AnyFrameMeta> Inv for LinkedListOwner<M> {
    open spec fn inv(&self) -> bool
    {
        forall |i:int|
            0 <= i < self.list.len() ==>
            self.inv_at(i)
    }
}

impl<M: AnyFrameMeta> LinkedListOwner<M> {
    pub open spec fn inv_at(self, i: int) -> bool
    {
        &&& self.list[i].prev is None <==> i == 0
        &&& self.list[i].next is None <==> i == self.list.len() - 1
        &&& self.perms.contains_key(i)
        &&& self.perms[i]@.is_init()
        &&& self.perms[i]@.mem_contents().value().wf(&self.list[i])
        &&& 0 < i ==>
            self.list[i].prev.is_some() &&
            self.perms[i-1]@.pptr() == self.list[i].prev.unwrap()
        &&& i < self.list.len() - 1 ==>
            self.list[i].next.is_some() &&
            self.perms[i+1]@.pptr() == self.list[i].next.unwrap()
        &&& self.list[i].inv()
        &&& self.list[i].slot@.in_list == self.list_id
    }

    pub open spec fn view_helper(owners: Seq<LinkOwner<M>>) -> Seq<LinkModel<M>>
        decreases owners.len()
    {
        if owners.len() == 0 {
            Seq::<LinkModel<M>>::empty()
        } else {
            seq![owners[0].view()].add(Self::view_helper(owners.remove(0)))
        }
    }

    pub proof fn view_preserves_len(owners: Seq<LinkOwner<M>>)
        ensures Self::view_helper(owners).len() == owners.len()
        decreases owners.len()
    {
        if owners.len() == 0 {

        } else {
            Self::view_preserves_len(owners.remove(0))
        }
    }
}

impl<M: AnyFrameMeta> InvView for LinkedListOwner<M> {
    type V = LinkedListModel<M>;

    open spec fn view(&self) -> Self::V {
        LinkedListModel::<M> {
            list: Self::view_helper(self.list)
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta> LinkedListOwner<M> {
    pub open spec fn update_prev(links: Seq<LinkOwner<M>>, i: int, prev: Option<PPtr<Link<M>>>) -> Seq<LinkOwner<M>> {
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
    }
}

impl<M: AnyFrameMeta> OwnerOf for LinkedList<M> {
    type Owner = LinkedListOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==>
            self.front is Some &&
            owner.perms[0]@.pptr() == self.front.unwrap() &&
            self.back is Some &&
            owner.perms[owner.list.len()-1]@.pptr() == self.back.unwrap()
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
}

impl<M: AnyFrameMeta> ModelOf for LinkedList<M> { }

impl<M: AnyFrameMeta> LinkedListModel<M> {
    pub open spec fn update_prev(links: Seq<LinkModel<M>>, i: int, prev: Option<PPtr<Link<M>>>) -> Seq<LinkModel<M>> {
        let link = links[i];
        let new_link = LinkModel::<M> {
            prev: prev,
            ..link
        };
        links.update(i, new_link)
    }

    pub open spec fn update_next(links: Seq<LinkModel<M>>, i: int, next: Option<PPtr<Link<M>>>) -> Seq<LinkModel<M>> {
        let link = links[i];
        let new_link = LinkModel::<M> {
            next: next,
            ..link
        };
        links.update(i, new_link)
    }
}

#[rustc_has_incoherent_inherent_impls]
pub ghost struct CursorModel<M: AnyFrameMeta> {
    pub ghost fore: Seq<LinkModel<M>>,
    pub ghost rear: Seq<LinkModel<M>>,
    pub ghost list_model: LinkedListModel<M>
}

impl<M: AnyFrameMeta> Inv for CursorModel<M> {
    open spec fn inv(&self) -> bool { self.list_model.inv() }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorOwner<M: AnyFrameMeta> {
    pub list_own: LinkedListOwner<M>,

    pub length: int,
    pub index: int,
    pub remaining: int,
}

impl<M: AnyFrameMeta> Inv for CursorOwner<M> {
    open spec fn inv(&self) -> bool {
        &&& self.length == self.list_own.list.len()
        &&& self.length == self.index + self.remaining
        &&& 0 <= self.index <= self.length
        &&& 0 <= self.remaining <= self.length
        &&& 0 <= self.length
        &&& self.list_own.inv()
    }
}

impl<M: AnyFrameMeta> InvView for CursorOwner<M> {
    type V = CursorModel<M>;

    open spec fn view(&self) -> Self::V {
        let list = self.list_own.view();
        CursorModel::<M> {
            fore: list.list.take(self.index),
            rear: list.list.skip(self.index),
            list_model: list,
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta> OwnerOf for CursorMut<M> {
    type Owner = CursorOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool
    {
//        &&& FRAME_METADATA_RANGE().start <= self.current.unwrap().addr() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE()
        &&& 0 <= owner.index < owner.list_own.list.len() ==>
                self.current.is_some() &&
                owner.list_own.perms[owner.index]@.pptr() == self.current.unwrap()
        &&& owner.index == owner.list_own.list.len() ==>
                self.current.is_none()
        &&& owner.list_own.self_perm@.pptr() == self.list
        &&& owner.list_own.self_perm@.is_init()
        &&& owner.list_own.self_perm@.mem_contents().value().wf(&owner.list_own)
    }
}

impl<M: AnyFrameMeta> ModelOf for CursorMut<M> { }

impl<M: AnyFrameMeta> CursorModel<M> {
    pub open spec fn current(self) -> Option<LinkModel<M>> {
        if self.rear.len() > 0 {
            Some(self.rear[0])
        } else {
            None
        }
    }
}

impl<M: AnyFrameMeta> CursorOwner<M> {
    pub open spec fn current(self) -> Option<LinkOwner<M>> {
        if 0 <= self.index < self.length {
            Some(self.list_own.list[self.index])
        } else {
            None
        }
    }

    pub open spec fn front_owner_spec(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            length: list_own.list.len() as int,
            index: 0,
            remaining: list_own.list.len() as int,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn front_owner(list_own: LinkedListOwner<M>) -> (res:Self)
        ensures
            res == Self::front_owner_spec(list_own)
    {
        CursorOwner::<M> {
            list_own: list_own,
            length: list_own.list.len() as int,
            index: 0,
            remaining: list_own.list.len() as int,
        }
    }

    pub open spec fn back_owner_spec(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            length: list_own.list.len() as int,
            index: list_own.list.len() as int - 1,
            remaining: 1,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn back_owner(list_own: LinkedListOwner<M>) -> (res:Self)
        ensures
            res == Self::back_owner_spec(list_own)
    {
        CursorOwner::<M> {
            list_own: list_own,
            length: list_own.list.len() as int,
            index: list_own.list.len() as int - 1,
            remaining: 1,
        }
    }

    pub open spec fn ghost_owner_spec(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            length: list_own.list.len() as int,
            index: list_own.list.len() as int,
            remaining: 0,
        }
    }

    #[verifier::returns(proof)]
    #[verifier::external_body]
    pub proof fn ghost_owner(list_own: LinkedListOwner<M>) -> (res:Self)
        ensures
            res == Self::ghost_owner_spec(list_own)
    {
        CursorOwner::<M> {
            list_own: list_own,
            length: list_own.list.len() as int,
            index: list_own.list.len() as int,
            remaining: 0,
        }
    }

/*    #[verifier::returns(proof)]
    pub proof fn cur_own(self) -> Tracked<PointsTo<Link<M>>>
        requires
            0 <= self.index < self.length
    {
        self.list_own.list[self.index].self_perm
    }*/
}

}