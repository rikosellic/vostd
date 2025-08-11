use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::seq_lib::*;
use vstd_extra::ownership::*;

use crate::prelude::*;
use crate::prelude::MetaSlotStorage::FrameLink;
use crate::prelude::LinkedList;

verus! {

pub ghost struct LinkModel {
    pub paddr: Paddr,
    pub prev: Option<Link>,
    pub next: Option<Link>,
}

impl Inv for LinkModel {
    open spec fn inv(&self) -> bool { true }
}

pub tracked struct LinkOwner {
    pub paddr: Paddr,
    pub prev_perm: Option<Tracked<PointsTo<Link>>>,
    pub next_perm: Option<Tracked<PointsTo<Link>>>
}

impl LinkOwner {

    pub fn get_next(self) -> Tracked<PointsTo<Link>>
        requires
            self.next_perm.is_some()
    {
        self.next_perm.unwrap()
    }

    pub fn get_prev(self) -> Tracked<PointsTo<Link>>
        requires
            self.next_perm.is_some()
    {
        self.next_perm.unwrap()
    }
}

impl Inv for LinkOwner {
    open spec fn inv(&self) -> bool { true }
}

impl InvView for LinkOwner {
    type V = LinkModel;

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

impl OwnerOf for Link {
    type Owner = LinkOwner;

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

impl ModelOf for Link { }

pub ghost struct LinkedListModel {
    pub list: Seq<LinkModel>,
//    pub links: Map<Paddr, LinkModel>,
}

impl LinkedListModel {
    pub open spec fn front(&self) -> Option<LinkModel> {
        if self.list.len() > 0 {
            Some(self.list[0])
        } else {
            None
        }
    }

    pub open spec fn back(&self) -> Option<LinkModel> {
        if self.list.len() > 0 {
            Some(self.list[self.list.len() - 1])
        } else {
            None
        }
    }

}

impl Inv for LinkedListModel {
    open spec fn inv(&self) -> bool { true }
}

pub tracked struct LinkedListOwner {
    pub list: Seq<LinkOwner>,
    pub front_perm: Option<Tracked<PointsTo<Link>>>,
    pub back_perm: Option<Tracked<PointsTo<Link>>>,
}

impl Inv for LinkedListOwner {
    open spec fn inv(&self) -> bool
    {
        forall |i:int|
            0 <= i < self.list.len() ==>
            Self::inv_at(self.list, i)
    }
}

impl LinkedListOwner {
    pub open spec fn inv_at(owners: Seq<LinkOwner>, i: int) -> bool
    {
        &&& owners[i].prev_perm.is_some() ==>
            owners[i].prev_perm.unwrap()@.is_init() &&
            owners[i].prev_perm.unwrap()@.mem_contents().value().wf(&owners[i-1])
        &&& owners[i].next_perm.is_some() ==>
            owners[i].next_perm.unwrap()@.is_init() &&
            owners[i].next_perm.unwrap()@.mem_contents().value().wf(&owners[i+1])
    }

    pub open spec fn view_helper(owners: Seq<LinkOwner>) -> Seq<LinkModel>
        decreases owners.len()
    {
        if owners.len() == 0 {
            Seq::<LinkModel>::empty()
        } else {
            seq![owners[0].view()].add(Self::view_helper(owners.remove(0)))
        }
    }

    pub proof fn view_preserves_len(owners: Seq<LinkOwner>)
        ensures Self::view_helper(owners).len() == owners.len()
        decreases owners.len()
    {
        if owners.len() == 0 {

        } else {
            Self::view_preserves_len(owners.remove(0))
        }
    }
}

impl InvView for LinkedListOwner {
    type V = LinkedListModel;

    open spec fn view(&self) -> Self::V {
        LinkedListModel {
            list: Self::view_helper(self.list)
        }
    }

    proof fn view_preserves_inv(&self) { }
}

impl OwnerOf for LinkedList {
    type Owner = LinkedListOwner;

    open spec fn wf(&self, owner: &Self::Owner) -> bool { true }
}

impl ModelOf for LinkedList { }

impl LinkedListModel {
    pub open spec fn update_prev(links: Seq<LinkModel>, i: int, prev: Option<Link>) -> Seq<LinkModel> {
        let link = links[i];
        let new_link = LinkModel {
            prev: prev,
            ..link
        };
        links.update(i, new_link)
    }

    pub open spec fn update_next(links: Seq<LinkModel>, i: int, next: Option<Link>) -> Seq<LinkModel> {
        let link = links[i];
        let new_link = LinkModel {
            next: next,
            ..link
        };
        links.update(i, new_link)
    }
}

pub ghost struct CursorModel {
    pub ghost fore: Seq<LinkModel>,
    pub ghost rear: Seq<LinkModel>,
    pub ghost list_model: LinkedListModel
}

impl Inv for CursorModel {
    open spec fn inv(&self) -> bool { self.list_model.inv() }
}

pub tracked struct CursorOwner {
    pub cur_own: LinkOwner,
    pub list_own: LinkedListOwner,

    pub cur_perm: Option<Tracked<PointsTo<Link>>>,
    pub prev_perm: Option<Tracked<PointsTo<Link>>>,
    pub next_perm: Option<Tracked<PointsTo<Link>>>,
    pub list_perm: Tracked<PointsTo<LinkedList>>,

    pub length: int,
    pub index: int,
    pub remaining: int,
}

impl Inv for CursorOwner {
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

impl InvView for CursorOwner {
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

impl OwnerOf for CursorMut {
    type Owner = CursorOwner;

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

impl ModelOf for CursorMut { }

impl CursorModel {

    pub open spec fn current(self) -> Option<LinkModel> {
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
                fore: Seq::<LinkModel>::empty(),
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
                rear: Seq::<LinkModel>::empty(),
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

    pub open spec fn insert(self, link: LinkModel) -> Self {
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

impl CursorOwner {
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