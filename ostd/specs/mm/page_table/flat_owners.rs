//! Flat ownership model for page tables.
//!
//! Unlike `OwnerSubtree`, this model does not recursively own child
//! `NodeOwner`s. A node entry records only the physical address of its child;
//! the corresponding linear resources live in `FlatPageTableOwner::nodes`.

use vstd::prelude::*;
use vstd_extra::{ghost_tree::TreePath, ownership::*};

use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::mm::page_table::{PageTableConfig, PageTableEntryTrait};
use crate::mm::{Paddr, PagingLevel, page_size};
use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS, valid_frame_paddr};
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::node::entry_owners::FrameEntryOwner;
use crate::specs::mm::page_table::node::owners::NodeOwner;

verus! {

/// Ownership of one PTE in the flat model. The node variant deliberately
/// contains only an address; its `NodeOwner` is stored in the node map.
pub tracked enum FlatEntryOwnerKind<C: PageTableConfig> {
    Node(ghost Paddr),
    Frame(FrameEntryOwner<C>),
    Borrowed(ghost Set<Mapping>),
    Absent,
}

pub tracked struct FlatEntryOwner<C: PageTableConfig> {
    pub kind: FlatEntryOwnerKind<C>,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost parent_level: PagingLevel,
}

impl<C: PageTableConfig> FlatEntryOwner<C> {
    pub open spec fn is_node(self) -> bool {
        self.kind is Node
    }

    pub open spec fn is_frame(self) -> bool {
        self.kind is Frame
    }

    pub open spec fn is_borrowed(self) -> bool {
        self.kind is Borrowed
    }

    pub open spec fn is_absent(self) -> bool {
        self.kind is Absent
    }

    pub open spec fn child_paddr(self) -> Paddr
        recommends self.is_node(),
    {
        self.kind->Node_0
    }

    pub open spec fn frame(self) -> FrameEntryOwner<C>
        recommends self.is_frame(),
    {
        self.kind->Frame_0
    }

    pub open spec fn borrowed(self) -> Set<Mapping>
        recommends self.is_borrowed(),
    {
        self.kind->Borrowed_0
    }

    pub open spec fn frame_permission(self) -> Option<C::Perm>
        recommends self.is_frame(),
    {
        self.frame().permission
    }

    pub open spec fn match_pte(self, pte: C::E) -> bool {
        &&& valid_frame_paddr(pte.paddr())
        &&& !pte.is_present() ==> {
            &&& self.is_absent()
            &&& self.parent_level > 1 ==> !pte.is_last(self.parent_level)
        }
        &&& pte.is_present() && !pte.is_last(self.parent_level) ==> {
            &&& self.is_node()
            &&& self.child_paddr() == pte.paddr()
        }
        &&& pte.is_present() && pte.is_last(self.parent_level) ==> {
            &&& self.is_frame()
            &&& self.frame().mapped_pa == pte.paddr()
            &&& self.frame().prop == pte.prop()
        }
    }

    pub open spec fn borrowed_match_pte(self, pte: C::E) -> bool {
        &&& self.is_borrowed()
        &&& valid_frame_paddr(pte.paddr())
        &&& pte.is_present()
        &&& !pte.is_last(self.parent_level)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.path.inv()
        &&& 1 <= self.parent_level <= NR_LEVELS
        &&& self.is_node() ==> {
            &&& 1 < self.parent_level
            &&& valid_frame_paddr(self.child_paddr())
        }
        &&& self.is_frame() ==> {
            &&& self.parent_level < NR_LEVELS
            &&& valid_frame_paddr(self.frame().mapped_pa)
            &&& self.frame().mapped_pa % page_size(self.parent_level) == 0
            &&& self.frame().mapped_pa + page_size(self.parent_level) <= MAX_PADDR
            &&& C::raw_item_well_formed((
                self.frame().mapped_pa,
                self.parent_level,
                self.frame().prop,
                Tracked(self.frame_permission()),
            ))
            &&& C::E::new_page_req(
                self.frame().mapped_pa,
                self.parent_level,
                self.frame().prop,
            )
        }
    }

    pub open spec fn new_absent(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> Self {
        Self { kind: FlatEntryOwnerKind::Absent, path, parent_level }
    }

    pub proof fn tracked_new_absent(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> (tracked result: Self)
        returns Self::new_absent(path, parent_level),
    {
        Self { kind: FlatEntryOwnerKind::Absent, path, parent_level }
    }

    pub open spec fn new_node(
        child: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> Self {
        Self { kind: FlatEntryOwnerKind::Node(child), path, parent_level }
    }

    pub proof fn tracked_new_node(
        child: Paddr,
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> (tracked result: Self)
        returns Self::new_node(child, path, parent_level),
    {
        Self { kind: FlatEntryOwnerKind::Node(child), path, parent_level }
    }
}

/// Linear resources and PTE owners for one physical page-table node.
pub tracked struct FlatNodeRecord<C: PageTableConfig> {
    pub node: NodeOwner<C>,
    pub entries: Seq<FlatEntryOwner<C>>,
    pub ghost path: TreePath<NR_ENTRIES>,
}

impl<C: PageTableConfig> FlatNodeRecord<C> {
    pub open spec fn paddr(self) -> Paddr {
        meta_to_frame(self.node.slot_vaddr())
    }

    pub open spec fn local_inv(self) -> bool {
        &&& self.node.inv()
        &&& self.path.inv()
        &&& self.entries.len() == NR_ENTRIES
        &&& forall|i: int| 0 <= i < NR_ENTRIES ==> {
            let entry = #[trigger] self.entries[i];
            let pte = self.node.children_perm.value()[i];
            &&& entry.inv()
            &&& entry.path == self.path.push_tail(i)
            &&& entry.parent_level == self.node.level()
            &&& entry.match_pte(pte) || (
                self.node.level() == NR_LEVELS
                    && C::LEADING_BITS_spec() == 0
                    && entry.borrowed_match_pte(pte)
            )
        }
    }

    pub open spec fn new(
        node: NodeOwner<C>,
        entries: Seq<FlatEntryOwner<C>>,
        path: TreePath<NR_ENTRIES>,
    ) -> Self {
        Self { node, entries, path }
    }

    pub proof fn tracked_new(
        tracked node: NodeOwner<C>,
        tracked entries: Seq<FlatEntryOwner<C>>,
        path: TreePath<NR_ENTRIES>,
    ) -> (tracked result: Self)
        returns Self::new(node, entries, path),
    {
        Self { node, entries, path }
    }
}

/// Flat authoritative ownership of one page table.
pub tracked struct FlatPageTableOwner<C: PageTableConfig> {
    pub ghost root: Paddr,
    pub nodes: Map<Paddr, FlatNodeRecord<C>>,
}

impl<C: PageTableConfig> FlatPageTableOwner<C> {
    pub open spec fn new(root: Paddr, record: FlatNodeRecord<C>) -> Self {
        Self { root, nodes: Map::empty().insert(root, record) }
    }

    pub proof fn tracked_new(
        root: Paddr,
        tracked record: FlatNodeRecord<C>,
    ) -> (tracked result: Self)
        returns Self::new(root, record),
    {
        let tracked mut nodes = Map::tracked_empty();
        nodes.tracked_insert(root, record);
        Self { root, nodes }
    }

    pub open spec fn contains_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr)
    }

    pub open spec fn node(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends self.contains_node(paddr),
    {
        self.nodes[paddr]
    }

    pub open spec fn local_node_inv(self, paddr: Paddr) -> bool {
        &&& self.contains_node(paddr)
        &&& self.node(paddr).paddr() == paddr
        &&& self.node(paddr).local_inv()
        &&& forall|i: int| 0 <= i < NR_ENTRIES ==> {
            let entry = #[trigger] self.node(paddr).entries[i];
            entry.is_node() ==> {
                &&& self.contains_node(entry.child_paddr())
                &&& self.node(entry.child_paddr()).path == entry.path
                &&& self.node(entry.child_paddr()).node.level() + 1
                    == self.node(paddr).node.level()
            }
        }
    }

    /// Paging level decreases on every node edge, bounding recursion.
    pub open spec fn subtree_inv_at(self, paddr: Paddr, depth: nat) -> bool
        decreases depth,
    {
        &&& self.local_node_inv(paddr)
        &&& self.node(paddr).node.level() == depth
        &&& if depth == 0 {
            false
        } else {
            forall|i: int| 0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] self.node(paddr).entries[i];
                entry.is_node() ==> self.subtree_inv_at(
                    entry.child_paddr(),
                    (depth - 1) as nat,
                )
            }
        }
    }

    pub open spec fn reachable_from(
        self,
        from: Paddr,
        target: Paddr,
        depth: nat,
    ) -> bool
        decreases depth,
    {
        from == target || (depth > 0 && self.contains_node(from) && exists|i: int|
            0 <= i < NR_ENTRIES && {
                let entry = #[trigger] self.node(from).entries[i];
                entry.is_node() && self.reachable_from(
                    entry.child_paddr(),
                    target,
                    (depth - 1) as nat,
                )
            })
    }

    pub open spec fn unique_parent(self) -> bool {
        forall|parent1: Paddr, parent2: Paddr, i: int, j: int|
            self.contains_node(parent1)
                && self.contains_node(parent2)
                && 0 <= i < NR_ENTRIES
                && 0 <= j < NR_ENTRIES
                && (#[trigger] self.node(parent1).entries[i]).is_node()
                && (#[trigger] self.node(parent2).entries[j]).is_node()
                && self.node(parent1).entries[i].child_paddr()
                    == self.node(parent2).entries[j].child_paddr()
                ==> parent1 == parent2 && i == j
    }

    pub open spec fn root_has_no_parent(self) -> bool {
        forall|parent: Paddr, i: int|
            self.contains_node(parent)
                && 0 <= i < NR_ENTRIES
                && (#[trigger] self.node(parent).entries[i]).is_node()
                ==> self.node(parent).entries[i].child_paddr() != self.root
    }

    pub open spec fn all_nodes_reachable(self) -> bool {
        forall|paddr: Paddr| #[trigger] self.contains_node(paddr) ==> self.reachable_from(
            self.root,
            paddr,
            NR_LEVELS as nat,
        )
    }

    pub open spec fn subtree_nodes(self, root: Paddr) -> Set<Paddr> {
        self.nodes.dom().filter(
            |paddr: Paddr| self.reachable_from(root, paddr, NR_LEVELS as nat),
        )
    }

    pub open spec fn inv(self) -> bool {
        &&& self.contains_node(self.root)
        &&& self.node(self.root).path == TreePath::<NR_ENTRIES>::new(Seq::empty())
        &&& self.subtree_inv_at(self.root, NR_LEVELS as nat)
        &&& self.unique_parent()
        &&& self.root_has_no_parent()
        &&& self.all_nodes_reachable()
    }

    pub proof fn tracked_borrow_node<'a>(
        tracked &'a self,
        paddr: Paddr,
    ) -> (tracked node: &'a FlatNodeRecord<C>)
        requires self.contains_node(paddr),
        ensures *node == self.node(paddr),
    {
        self.nodes.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_subtree<'a>(
        tracked &'a self,
        root: Paddr,
    ) -> (tracked subtree: FlatOwnerSubtree<'a, C>)
        requires self.contains_node(root),
        ensures
            subtree.root == root,
            *subtree.owner == *self,
    {
        FlatOwnerSubtree { owner: self, root }
    }

    /// Borrow a subtree by splitting the flat map. No `NodeOwner` is removed
    /// or moved; the complement remains borrowed in `remainder`.
    pub proof fn tracked_borrow_subtree_mut<'a>(
        tracked &'a mut self,
        root: Paddr,
    ) -> (tracked subtree: FlatOwnerSubtreeMut<'a, C>)
        requires old(self).contains_node(root),
        ensures
            subtree.root == root,
            *subtree.nodes == old(self).nodes.restrict(old(self).subtree_nodes(root)),
            *subtree.remainder == old(self).nodes.remove_keys(old(self).subtree_nodes(root)),
    {
        let ghost keys = self.subtree_nodes(root);
        assert(keys <= self.nodes.dom());
        let tracked (nodes, remainder) = self.nodes.tracked_borrow_mut_split(keys);
        FlatOwnerSubtreeMut { nodes, remainder, root }
    }

    pub proof fn tracked_insert_node(
        tracked &mut self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
    )
        requires
            !old(self).contains_node(paddr),
            record.paddr() == paddr,
        ensures
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(paddr, record),
    {
        self.nodes.tracked_insert(paddr, record);
    }

    pub proof fn tracked_remove_node(
        tracked &mut self,
        paddr: Paddr,
    ) -> (tracked record: FlatNodeRecord<C>)
        requires
            old(self).contains_node(paddr),
            paddr != old(self).root,
        ensures
            record == old(self).node(paddr),
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.remove(paddr),
    {
        self.nodes.tracked_remove(paddr)
    }
}

/// Immutable borrowed subtree: a store reference plus a root address.
pub tracked struct FlatOwnerSubtree<'a, C: PageTableConfig> {
    pub owner: &'a FlatPageTableOwner<C>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatOwnerSubtree<'a, C> {
    pub open spec fn inv(self) -> bool {
        self.owner.contains_node(self.root)
    }

    pub open spec fn record(self) -> FlatNodeRecord<C>
        recommends self.inv(),
    {
        self.owner.node(self.root)
    }

    pub open spec fn entry(self, idx: int) -> FlatEntryOwner<C>
        recommends
            self.inv(),
            0 <= idx < NR_ENTRIES,
    {
        self.record().entries[idx]
    }

    pub proof fn tracked_child(
        tracked &self,
        idx: int,
    ) -> (tracked child: FlatOwnerSubtree<'a, C>)
        requires
            self.inv(),
            self.owner.local_node_inv(self.root),
            0 <= idx < NR_ENTRIES,
            self.entry(idx).is_node(),
        ensures
            child.inv(),
            child.root == self.entry(idx).child_paddr(),
            *child.owner == *self.owner,
    {
        FlatOwnerSubtree { owner: self.owner, root: self.entry(idx).child_paddr() }
    }
}

/// Mutable borrow of a subtree and the disjoint complement of its node map.
pub tracked struct FlatOwnerSubtreeMut<'a, C: PageTableConfig> {
    pub nodes: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub remainder: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatOwnerSubtreeMut<'a, C> {
    pub open spec fn contains_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr)
    }

    pub open spec fn record(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends self.contains_node(paddr),
    {
        self.nodes[paddr]
    }

    pub proof fn tracked_borrow_node(
        tracked &self,
        paddr: Paddr,
    ) -> (tracked node: &FlatNodeRecord<C>)
        requires self.contains_node(paddr),
        ensures *node == self.record(paddr),
    {
        self.nodes.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_node_mut(
        tracked &mut self,
        paddr: Paddr,
    ) -> (tracked node: &mut FlatNodeRecord<C>)
        requires old(self).contains_node(paddr),
        ensures
            *node == old(self).record(paddr),
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).nodes == old(self).nodes.insert(paddr, *final(node)),
    {
        self.nodes.tracked_borrow_mut(paddr)
    }
}

} // verus!
