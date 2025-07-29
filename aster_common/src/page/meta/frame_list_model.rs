use vstd::prelude::*;
use vstd::simple_pptr::*;
//use vstd::
use crate::prelude::*;
use crate::prelude::MetaSlotStorage::FrameLink;
use crate::prelude::LinkedList;

verus! {

pub ghost struct LinkModel {
    pub paddr: Paddr,
    pub ghost prev_perm: Option<PointsTo<Link>>,
    pub ghost next_perm: Option<PointsTo<Link>>
}

impl LinkModel {
    pub open spec fn relate(self, link: Link) -> bool {
        &&& self.prev_perm.is_some() <==> link.prev.is_some()
        &&& self.prev_perm.unwrap().pptr() == link.prev.unwrap()
        &&& self.next_perm.is_some() <==> link.next.is_some()
        &&& self.next_perm.unwrap().pptr() == link.next.unwrap()
    }
}

pub ghost struct LinkedListModel {
    pub list: Seq<Paddr>,
    pub links: Map<Paddr, LinkModel>,
    pub front: Option<PointsTo<Link>>,
    pub back: Option<PointsTo<Link>>,
}

impl LinkedListModel {
    pub open spec fn wf_at(self, i: int) -> bool {
        let p = self.list[i];
        let model = self.links[p];
        &&& i > 0 ==> (model.prev_perm.is_some() && model.prev_perm.unwrap().pptr().addr() == self.list[i-1])
        &&& i < self.list.len() - 1 ==> (model.next_perm.is_some() && model.next_perm.unwrap().pptr().addr() == self.list[i+1])
    }

    pub open spec fn wf(self) -> bool {
        &&& self.front.unwrap().pptr().addr() == self.list[0]
        &&& self.back.unwrap().pptr().addr() == self.list[self.list.len() - 1]
        &&& forall |i:int|
                0 <= i < self.list.len() ==>
                self.wf_at(i)
    }

    pub open spec fn relate_help(self, i: usize, link: Link, meta_region: MetaRegionModel) -> bool
        decreases i
    {
        let p = self.list[(self.list.len() - i) as int];
        let slot = meta_region.slots[p];
        let link_model = self.links[p];
        if let FrameLink(link) = slot.storage.value() {
            if i == 0 {
                link_model.relate(link)
            } else {
                link_model.relate(link) &&
                self.relate_help((i-1) as usize, link_model.next_perm.unwrap().mem_contents().value(), meta_region)
            }
        } else {
            false
        }
    }

    pub open spec fn relate(self, linked_list: LinkedList, meta_region: MetaRegionModel) -> bool {
        &&& self.front.unwrap().pptr() == linked_list.front.unwrap()
        &&& self.list.len() == linked_list.size
        &&& self.relate_help(self.list.len() as usize, self.front.unwrap().mem_contents().value(), meta_region)
    }

    pub open spec fn update_prev(links: Map<Paddr, LinkModel>, p: Paddr, perm: Option<PointsTo<Link>>) -> Map<Paddr, LinkModel> {
        let link = links[p];
        let new_link = LinkModel {
            prev_perm: perm,
            ..link
        };
        links.insert(p, new_link)
    }

    pub open spec fn update_next(links: Map<Paddr, LinkModel>, p: Paddr, perm: Option<PointsTo<Link>>) -> Map<Paddr, LinkModel> {
        let link = links[p];
        let new_link = LinkModel {
            next_perm: perm,
            ..link
        };
        links.insert(p, new_link)
    }

}

pub ghost struct CursorModel {
    pub ghost front: Seq<Paddr>,
    pub ghost back: Seq<Paddr>,
    pub ghost cur_perm: Option<PointsTo<Link>>,
    pub ghost list_model: LinkedListModel
}

impl CursorModel {

    pub open spec fn relate(self, cursor: CursorMut) -> bool {
        true
    }

    pub open spec fn current(self) -> Option<Paddr> {
        if self.back.len() > 0 {
            Some(self.back[0])
        } else {
            None
        }
    }

    pub open spec fn move_next_spec(self) -> Self {
        if self.back.len() > 0 {
            let cur = self.back[0];
            Self {
                front: self.front.insert(self.front.len() as int, cur),
                back: self.back.remove(0),
                cur_perm: self.list_model.links[cur].next_perm,
                list_model: self.list_model
            }
        } else {
            Self {
                front: Seq::<Paddr>::empty(),
                back: self.front,
                cur_perm: self.list_model.front,
                list_model: self.list_model
            }
        }
    }

    pub open spec fn move_prev_spec(self) -> Self {
        if self.front.len() > 0 {
            let cur = self.front[self.front.len()-1];
            Self {
                front: self.front.remove(self.front.len()-1),
                back: self.back.insert(0, cur),
                cur_perm: self.list_model.links[cur].prev_perm,
                list_model: self.list_model
            }
        } else {
            Self {
                front: self.back,
                back: Seq::<Paddr>::empty(),
                cur_perm: self.list_model.back,
                list_model: self.list_model
            }
        }
    }

    pub open spec fn remove(self) -> Self {
        let paddr = self.current().unwrap();
        let link_model = self.list_model.links[self.back[0]];
        let links = self.list_model.links.remove(paddr);
        let links = if self.front.len() > 0  { LinkedListModel::update_next(links, self.front[self.front.len()-1], link_model.next_perm) } else { links };
        let links = if self.back.len()  > 0  { LinkedListModel::update_prev(links, self.back[0], link_model.prev_perm) } else { links };
        let front_perm = if self.front.len() == 0 { link_model.next_perm } else { self.list_model.front };
        let back_perm  = if self.back.len()  == 0 { link_model.prev_perm } else { self.list_model.back };
        let back_list = self.back.remove(0);

        let list_model = LinkedListModel {
            list: self.front.add(back_list),
            links: links,
            front: front_perm,
            back: back_perm,
        };

        Self {
            front: self.front,
            back: back_list,
            cur_perm: link_model.next_perm,
            list_model: list_model,
        }
    }

    pub open spec fn insert(self, link_model: LinkModel) -> Self {
        let p = link_model.paddr;
        let links = self.list_model.links.insert(p, link_model);
        let links = if self.front.len() > 0 { LinkedListModel::update_next(links, self.front[self.front.len()-1], link_model.next_perm) } else { links };
        let links = if self.back.len() > 0 { LinkedListModel::update_prev(links, self.back[0], link_model.prev_perm) } else { links };
        let front_perm = if self.front.len() == 0 { link_model.next_perm } else { self.list_model.front };
        let back_perm = if self.back.len() == 0 { link_model.prev_perm } else { self.list_model.back };
        let front_list = self.front.insert(self.front.len() as int, p);

        let list_model = LinkedListModel {
            list: front_list.add(self.back),
            links: links,
            front: front_perm,
            back: back_perm,
        };

        Self {
            front: front_list,
            back: self.back,
            cur_perm: link_model.next_perm,
            list_model: list_model,
        }
    }
}

}