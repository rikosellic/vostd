use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::prelude::*;

verus! {

pub ghost struct LinkModel {
    pub paddr: Paddr,
    pub ghost prev_perm: Option<PointsTo<Link>>,
    pub ghost next_perm: Option<PointsTo<Link>>
}

pub ghost struct LinkedListModel {
    pub list: Seq<Paddr>,
    pub links: Map<Paddr, LinkModel>,
}

impl LinkedListModel {
    pub open spec fn wf_at(self, i: int) -> bool {
        let p = self.list[i];
        let model = self.links[p];
        &&& i > 0 ==> (model.prev_perm.is_some() && model.prev_perm.unwrap().pptr().addr() == self.list[i-1])
        &&& i < self.list.len() - 1 ==> (model.next_perm.is_some() && model.next_perm.unwrap().pptr().addr() == self.list[i+1])
    }

    pub open spec fn wf(self) -> bool {
        forall |i:int|
            0 <= i < self.list.len() ==>
            self.wf_at(i)
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

    pub open spec fn insert(self, i: int, perm: PointsTo<Link>, model: LinkModel) -> Self {
        let list = self.list.insert(i, model.paddr);
        let links = self.links.insert(model.paddr, model);
        let links = if 0 < i { Self::update_next(links, list[i-1], Some(perm)) } else { links };
        let links = if i < list.len() - 1 { Self::update_prev(links, list[i+1], Some(perm)) } else { links };
        Self {
            list: list,
            links: links,
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
    }
}

}