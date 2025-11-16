use vstd::prelude::*;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::TreeNodeValue;

use super::*;

use std::ops::Deref;

verus! {

/*
impl<'rcu, C: PageTableConfig> EntryState<'rcu, C> {
    open spec fn get_entry(self) -> Option<EntryOwner<'rcu, C>> {
        match self {
            Self::Present(owner) => Some(owner),
            _ => None,
        }
    }
}
*/

pub tracked struct OwnerInTree<'rcu, C: PageTableConfig> {
    pub tree_node: EntryOwner<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Inv for OwnerInTree<'rcu, C> {
    open spec fn inv(self) -> bool {
        true
/*        match self.tree_node {
            Self::Present(owner) => owner.inv(),
            Self::Absent => true,
            Self::Locked => true,
        }*/
    }
}

impl<'rcu, C: PageTableConfig> TreeNodeValue for EntryOwner<'rcu, C> {
    open spec fn default() -> Self {
        Self {
            as_child: ChildOwner { node:None, frame:None, locked:None },
            index: 0,
            base_addr: 0,
            path: Ghost(Seq::empty())
        }
    }

    proof fn default_preserves_inv()
        ensures
            #[trigger] Self::default().inv(),
    { }
}

pub tracked struct OwnerAsTreeNode<'rcu, C: PageTableConfig> {
    pub inner: Node<EntryOwner<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>,
}

impl<'rcu, C: PageTableConfig> Deref for OwnerAsTreeNode<'rcu, C> {
    type Target = Node<EntryOwner<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'rcu, C: PageTableConfig> OwnerAsTreeNode<'rcu, C> {
    pub open spec fn is_leaf(self) -> bool {
        &&& self.inner.value.as_child.is_frame()
//        &&& self.value.get_entry().unwrap().node_owner.meta_own.nr_children@
        &&& self.inner.children.len() == 0
    }
}

impl<'rcu, C: PageTableConfig> OwnerAsTreeNode<'rcu, C> {
    pub open spec fn valid_ptrs(self) -> bool {
        forall|i: usize| #![auto]
            0 <= i < NR_ENTRIES() ==> self.inner.children[i as int] is Some ==> {
                &&& self.inner.value.as_child.node is Some
                &&& self.inner.value.as_child.node.unwrap().children_perm.is_init(i as int)
//                &&& self.inner.children[i as int].unwrap().value.tree_node is Some
                &&& self.inner.value.as_child.node.unwrap().children_perm.opt_value()[i as int].value().wf(
                    self.inner.children[i as int].unwrap().value)
            }
    }
}

#[verusfmt::skip]
pub tracked struct PageTableOwner<'rcu, C: PageTableConfig> {
    pub tree: OwnerAsTreeNode<'rcu, C>,
}

} // verus!
