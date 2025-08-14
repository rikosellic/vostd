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
    pub prev: Option<Link<M>>,
    pub next: Option<Link<M>>,
}

impl<M: AnyFrameMeta> Inv for LinkModel<M> {
    open spec fn inv(&self) -> bool { true }
}

pub tracked struct LinkOwner<M: AnyFrameMeta> {
    pub paddr: Paddr,
    pub prev_perm: Option<Tracked<PointsTo<Link<M>>>>,
    pub next_perm: Option<Tracked<PointsTo<Link<M>>>>
}

impl<M: AnyFrameMeta> LinkOwner<M> {

    pub fn get_next(self) -> Tracked<PointsTo<Link<M>>>
        requires
            self.next_perm.is_some()
    {
        self.next_perm.unwrap()
    }

    pub fn get_prev(self) -> Tracked<PointsTo<Link<M>>>
        requires
            self.next_perm.is_some()
    {
        self.next_perm.unwrap()
    }
}

impl<M: AnyFrameMeta> Inv for LinkOwner<M> {
    open spec fn inv(&self) -> bool { true }
}

impl<M: AnyFrameMeta> InvView for LinkOwner<M> {
    type V = LinkModel<M>;

    open spec fn view(&self) -> Self::V {
        let prev = if let Some(prev_perm) = self.prev_perm { Some(prev_perm@.mem_contents().value()) } else { None };
        let next = if let Some(next_perm) = self.next_perm { Some(next_perm@.mem_contents().value()) } else { None };
        LinkModel {
            paddr: self.paddr,
            prev: prev,
            next: next,
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl<M: AnyFrameMeta> OwnerOf for Link<M> {
    type Owner = LinkOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool {
        &&& owner.prev_perm.is_some() ==>
            self.prev.is_some() &&
            owner.prev_perm.unwrap()@.pptr() == self.prev.unwrap()
        &&& owner.next_perm.is_some() ==>
            self.next.is_some() &&
            owner.next_perm.unwrap()@.pptr() == self.next.unwrap()
        &&& owner.prev_perm.is_none() ==> self.prev.is_none()
        &&& owner.next_perm.is_none() ==> self.next.is_none()
    }
}

impl<M: AnyFrameMeta> ModelOf for Link<M> { }

pub ghost struct LinkedListModel<M: AnyFrameMeta> {
    pub list: Seq<LinkModel<M>>,
//    pub links: Map<Paddr, LinkModel>,
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
    pub front_perm: Option<Tracked<PointsTo<Link<M>>>>,
    pub back_perm: Option<Tracked<PointsTo<Link<M>>>>,
}

impl<M: AnyFrameMeta> Inv for LinkedListOwner<M> {
    open spec fn inv(&self) -> bool
    {
        forall |i:int|
            0 <= i < self.list.len() ==>
            Self::inv_at(self.list, i)
    }
}

impl<M: AnyFrameMeta> LinkedListOwner<M> {
    pub open spec fn inv_at(owners: Seq<LinkOwner<M>>, i: int) -> bool
    {
        &&& owners[i].prev_perm.is_some() ==>
            owners[i].prev_perm.unwrap()@.is_init() &&
            owners[i].prev_perm.unwrap()@.mem_contents().value().wf(&owners[i-1])
        &&& owners[i].next_perm.is_some() ==>
            owners[i].next_perm.unwrap()@.is_init() &&
            owners[i].next_perm.unwrap()@.mem_contents().value().wf(&owners[i+1])
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

impl<M: AnyFrameMeta> OwnerOf for LinkedList<M> {
    type Owner = LinkedListOwner<M>;

    open spec fn wf(&self, owner: &Self::Owner) -> bool { true }
}

impl<M: AnyFrameMeta> ModelOf for LinkedList<M> { }

impl<M: AnyFrameMeta> LinkedListModel<M> {
    pub open spec fn update_prev(links: Seq<LinkModel<M>>, i: int, prev: Option<Link<M>>) -> Seq<LinkModel<M>> {
        let link = links[i];
        let new_link = LinkModel::<M> {
            prev: prev,
            ..link
        };
        links.update(i, new_link)
    }

    pub open spec fn update_next(links: Seq<LinkModel<M>>, i: int, next: Option<Link<M>>) -> Seq<LinkModel<M>> {
        let link = links[i];
        let new_link = LinkModel::<M> {
            next: next,
            ..link
        };
        links.update(i, new_link)
    }
}

pub ghost struct CursorModel<M: AnyFrameMeta> {
    pub ghost fore: Seq<LinkModel<M>>,
    pub ghost rear: Seq<LinkModel<M>>,
    pub ghost list_model: LinkedListModel<M>
}

impl<M: AnyFrameMeta> Inv for CursorModel<M> {
    open spec fn inv(&self) -> bool { self.list_model.inv() }
}

pub tracked struct CursorOwner<M: AnyFrameMeta> {
    pub cur_own: LinkOwner<M>,
    pub list_own: LinkedListOwner<M>,

    pub cur_perm: Option<Tracked<PointsTo<Link<M>>>>,
    pub prev_perm: Option<Tracked<PointsTo<Link<M>>>>,
    pub next_perm: Option<Tracked<PointsTo<Link<M>>>>,
    pub list_perm: Tracked<PointsTo<LinkedList<M>>>,

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
        &&& self.next_perm.is_some() ==>
            self.cur_perm.is_some() &&
            self.cur_perm.unwrap()@.mem_contents().value().next == Some(self.next_perm.unwrap()@.pptr())
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
        &&& owner.cur_perm.is_some() ==>
                self.current.is_some() &&
                owner.cur_perm.unwrap()@.pptr() == self.current.unwrap() &&
                owner.cur_perm.unwrap()@.is_init() &&
                owner.next_perm == owner.list_own.list[owner.index].next_perm &&
                owner.remaining > 0
        &&& owner.cur_perm.is_none() ==>
                self.current.is_none() &&
                owner.remaining == 0
        &&& owner.list_perm@.pptr() == self.list
        &&& owner.list_perm@.is_init()
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

    pub open spec fn move_next_spec(self) -> Self {
        if self.rear.len() > 0 {
            let cur = self.rear[0];
            Self {
                fore: self.fore.insert(self.fore.len() as int, cur),
                rear: self.rear.remove(0),
                list_model: self.list_model
            }
        } else {
            Self {
                fore: Seq::<LinkModel<M>>::empty(),
                rear: self.fore,
                list_model: self.list_model
            }
        }
    }

    pub open spec fn move_prev_spec(self) -> Self {
        if self.fore.len() > 0 {
            let cur = self.fore[self.fore.len()-1];
            Self {
                fore: self.fore.remove(self.fore.len()-1),
                rear: self.rear.insert(0, cur),
                list_model: self.list_model
            }
        } else {
            Self {
                fore: self.rear,
                rear: Seq::<LinkModel<M>>::empty(),
                list_model: self.list_model
            }
        }
    }

    pub open spec fn remove(self) -> Self {
        let cur = self.current().unwrap();
        let rear = self.rear.remove(0);
        let rear = if rear.len() > 0 { LinkedListModel::update_prev(rear, 0, cur.prev) } else { rear };
        let fore = if self.fore.len() > 0 { LinkedListModel::update_next(self.fore, self.fore.len() - 1, cur.next) } else { self.fore };        

        Self {
            fore: fore,
            rear: rear,
            list_model: LinkedListModel { list: fore.add(rear) }
        }
    }

    pub open spec fn insert(self, link: LinkModel<M>) -> Self {
        let fore = self.fore.insert(self.fore.len() - 1, link);
        let rear = if self.rear.len() > 0 { LinkedListModel::update_prev(self.rear, 0, link.prev) } else { self.rear };
        let fore = if fore.len() > 0 { LinkedListModel::update_next(self.fore, self.fore.len() - 1, link.next) } else { fore };        
        
        Self {
            fore: fore,
            rear: rear,
            list_model: self.list_model
        }
    }
}

impl<M: AnyFrameMeta> CursorOwner<M> {
    /*
    pub cur_own: LinkOwner,
    pub list_own: LinkedListOwner,

    pub cur_perm: Option<Tracked<PointsTo<Link>>>,
    pub prev_perm: Tracked<PointsTo<Link>>,
    pub next_perm: Tracked<PointsTo<Link>>,
    pub list_perm: Tracked<PointsTo<LinkedList>>,

    pub length: int,
    pub index: int,
    pub remaining: int,
    */
    pub open spec fn move_next_owner_spec(self) -> Self {
        if self.remaining > 0 {
            Self {
                cur_own: self.list_own.list[self.index+1],
                list_own: self.list_own,
                cur_perm: self.next_perm,
                prev_perm: self.cur_perm,
                next_perm: self.list_own.list[self.index+1].next_perm,
                list_perm: self.list_perm,
                length: self.length,
                index: self.index+1,
                remaining: self.remaining-1,
            }
        } else {
            Self {
                cur_own: self.list_own.list[0],
                list_own: self.list_own,
                cur_perm: self.list_own.front_perm,
                prev_perm: None,
                next_perm: self.list_own.list[0].next_perm,
                list_perm: self.list_perm,
                length: self.length,
                index: 0,
                remaining: self.length,
            }
        }
    }
}

}