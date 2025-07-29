use vstd::prelude::*;
use vstd::simple_pptr::*;
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

/*    pub open spec fn insert(self, i: int, perm: PointsTo<Link>, model: LinkModel) -> Self {
        let list = self.list.insert(i, model.paddr);
        let links = self.links.insert(model.paddr, model);
        let links = if 0 < i { Self::update_next(links, list[i-1], Some(perm)) } else { links };
        let links = if i < list.len() - 1 { Self::update_prev(links, list[i+1], Some(perm)) } else { links };
        Self {
            list: list,
            links: links,
            ..self
        }
    }

    pub proof fn insert_len(self, i: int, perm: PointsTo<Link>, model: LinkModel)
        requires
            0 <= i <= self.list.len()
        ensures
            self.insert(i, perm, model).list.len() == self.list.len() + 1
    {}

    pub proof fn insert_preserves_inv(self, i: int, perm: PointsTo<Link>, model: LinkModel)
        requires
            self.wf(),
            0 <= i <= self.list.len(),
            0 < i ==> model.prev_perm.is_some() && model.prev_perm.unwrap().pptr().addr() == self.list[i-1],
            i < self.list.len() ==> model.next_perm.is_some() && model.next_perm.unwrap().pptr().addr() == self.list[i],
        ensures
            self.insert(i,perm,model).wf()
    {
        admit()
    }

    pub open spec fn remove(self, i: int) -> Self {
        let p = self.list[i];
        let model = self.links[p];
        let list = self.list.remove(i);
        let links = self.links.remove(p);
        let links = if 0 < i { Self::update_next(links, list[i-1], model.next_perm) } else { links };
        let links = if i < list.len() - 1 { Self::update_prev(links, list[i], model.prev_perm) } else { links };
        Self {
            list: list,
            links: links,
        }
    }

    pub proof fn remove_preserves_inv(self, i: int)
        requires
            self.wf(),
            0 <= i <= self.list.len(),
        ensures
            self.remove(i).wf()
    {
        admit()
    }*/
}

pub ghost struct CursorModel {
    pub ghost front: Seq<Paddr>,
    pub ghost back: Seq<Paddr>,
    pub ghost cur_perm: Option<PointsTo<Link>>
}

impl CursorModel {
    pub open spec fn current(self) -> Option<Paddr> {
        if self.back.len() > 0 {
            Some(self.back[0])
        } else {
            None
        }
    }

    pub open spec fn remove(self, list_model: LinkedListModel) -> (Self, LinkedListModel) {
        let paddr = self.current().unwrap();
        let link_model = list_model.links[self.back[0]];
        let cursor = Self {
            front: self.front,
            back: self.back.remove(0),
            cur_perm: link_model.next_perm,
        };
        let list = cursor.front.add(cursor.back);
        let links = list_model.links.remove(paddr);
        let idx = self.front.len();
        let links = if idx > 0 { LinkedListModel::update_next(links, self.front[idx-1], link_model.next_perm) } else { links };
        let links = if self.back.len() > 0 { LinkedListModel::update_prev(links, self.back[0], link_model.prev_perm) } else { links };
        let front = if idx == 0 { link_model.next_perm } else { list_model.front };
        let back = if self.back.len() == 0 { link_model.prev_perm } else { list_model.back };
        (cursor,
            LinkedListModel {
                list: list,
                links: links,
                front: front,
                back: back,
        })
    }

    pub open spec fn insert(self, link_model: LinkModel, list_model: LinkedListModel) -> (Self, LinkedListModel) {
        let p = link_model.paddr;
        let cursor = Self {
            front: self.front.insert(self.front.len() as int, p),
            back: self.back,
            cur_perm: self.cur_perm,
        };
        let list = cursor.front.add(cursor.back);
        let links = list_model.links.insert(p, link_model);
        let idx = self.front.len();
        let links = if idx > 0 { LinkedListModel::update_next(links, self.front[idx-1], link_model.next_perm) } else { links };
        let links = if self.back.len() > 0 { LinkedListModel::update_prev(links, self.back[0], link_model.prev_perm) } else { links };
        let front = if idx == 0 { link_model.next_perm } else { list_model.front };
        let back = if self.back.len() == 0 { link_model.prev_perm } else { list_model.back };
        (cursor,
            LinkedListModel {
                list: list,
                links: list_model.links.insert(p, link_model),
                back: list_model.back,
                front: list_model.front,
            }
        )
    }
}

}