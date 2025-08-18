use vstd::prelude::*;
use vstd_extra::prelude::*;
use aster_common::prelude::*;
use aster_common::prelude::frame_list_model::*;

verus! {

impl<M: AnyFrameMeta> CursorModel<M> {

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
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