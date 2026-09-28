//! Flat ownership model for page tables.
//!
//! Unlike `OwnerSubtree`, this model does not recursively own child
//! `NodeOwner`s. A node entry records only the physical address of its child;
//! the corresponding linear resources live in `FlatPageTableOwner::nodes`.
use vstd::prelude::*;
use vstd_extra::{array_ptr, ghost_tree::TreePath, ownership::*};

use crate::mm::frame::meta::{META_SLOT_SIZE, mapping::meta_to_frame};
use crate::mm::kspace::{FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR};
use crate::mm::page_table::{PageTableConfig, PageTableEntryTrait};
use crate::mm::{Paddr, PagingLevel, Vaddr, paddr_to_vaddr, page_size};
use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS, valid_frame_paddr};
use crate::specs::mm::frame::mapping::{index_to_meta, max_meta_slots};
use crate::specs::mm::frame::meta_owners::FracMetadataPerm;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::node::entry_owners::FrameEntryOwner;
use crate::specs::mm::page_table::node::owners::{NodeOwner, PageMetaOwner};
use crate::specs::mm::page_table::owners::INC_LEVELS;

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
        recommends
            self.is_node(),
    {
        self.kind->Node_0
    }

    pub open spec fn frame(self) -> FrameEntryOwner<C>
        recommends
            self.is_frame(),
    {
        self.kind->Frame_0
    }

    pub open spec fn borrowed(self) -> Set<Mapping>
        recommends
            self.is_borrowed(),
    {
        self.kind->Borrowed_0
    }

    pub open spec fn frame_permission(self) -> Option<C::Perm>
        recommends
            self.is_frame(),
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
            &&& C::raw_item_well_formed(
                (
                    self.frame().mapped_pa,
                    self.parent_level,
                    self.frame().prop,
                    Tracked(self.frame_permission()),
                ),
            )
            &&& C::E::new_page_req(self.frame().mapped_pa, self.parent_level, self.frame().prop)
        }
    }

    pub open spec fn new_absent(path: TreePath<NR_ENTRIES>, parent_level: PagingLevel) -> Self {
        Self { kind: FlatEntryOwnerKind::Absent, path, parent_level }
    }

    pub proof fn tracked_new_absent(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
    ) -> (tracked result: Self)
        returns
            Self::new_absent(path, parent_level),
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
        returns
            Self::new_node(child, path, parent_level),
    {
        Self { kind: FlatEntryOwnerKind::Node(child), path, parent_level }
    }
}

/// The structural resources of a page-table node.
///
/// In particular, this type does not contain a `FracMetadataPerm`.  The
/// permission is owned either by the live `Frame` (for the root or a detached
/// node), or by `FlatPageTableOwner::raw_node_permissions` while the node is
/// represented by a raw PTE.
pub tracked struct FlatNodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
    pub ghost level: PagingLevel,
    pub ghost tree_level: int,
    pub ghost slot_index: int,
}

impl<C: PageTableConfig> FlatNodeOwner<C> {
    pub open spec fn slot_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    pub open spec fn inv(self) -> bool {
        &&& self.meta_own.inv()
        &&& 0 <= self.meta_own.nr_children.value() <= NR_ENTRIES
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.children_perm.wf()
        &&& self.children_perm.is_init_all()
        &&& self.children_perm.addr() == paddr_to_vaddr(meta_to_frame(self.slot_vaddr()))
        &&& self.tree_level == INC_LEVELS - self.level - 1
        &&& 0 <= self.slot_index < max_meta_slots()
        &&& FRAME_METADATA_RANGE.start <= self.slot_vaddr() < FRAME_METADATA_RANGE.end
        &&& self.slot_vaddr() % META_SLOT_SIZE == 0
        &&& meta_to_frame(self.slot_vaddr()) < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR
        &&& meta_to_frame(self.slot_vaddr()) < MAX_PADDR
        &&& meta_to_frame(self.slot_vaddr()) == self.children_perm.addr()
    }

    pub open spec fn from_legacy(node: NodeOwner<C>) -> Self {
        Self {
            meta_own: node.meta_own,
            children_perm: node.children_perm,
            level: node.level(),
            tree_level: node.tree_level,
            slot_index: node.slot_index,
        }
    }

    /// Transitional adapter used while call sites still produce the old
    /// recursive `NodeOwner`.  It makes the important ownership transfer
    /// explicit: structural ownership and frame permission become independent
    /// tracked values.
    pub proof fn tracked_from_legacy(tracked node: NodeOwner<C>) -> (tracked (flat, permission): (
        Self,
        FracMetadataPerm,
    ))
        requires
            node.inv(),
        ensures
            flat == Self::from_legacy(node),
            flat.inv(),
            permission == node.frame_permission,
    {
        let ghost level = node.level();
        let tracked NodeOwner {
            meta_own,
            frame_permission,
            children_perm,
            tree_level,
            slot_index,
        } = node;
        (Self { meta_own, children_perm, level, tree_level, slot_index }, frame_permission)
    }

    /// Reassembles the transitional recursive owner when a raw node is taken
    /// back out of the flat store.  Keeping this operation explicit prevents
    /// the metadata permission from being forgotten on the raw-to-owned path.
    pub proof fn tracked_into_legacy(
        tracked self,
        tracked permission: FracMetadataPerm,
    ) -> (tracked node: NodeOwner<C>)
        ensures
            node.meta_own == self.meta_own,
            node.frame_permission == permission,
            node.children_perm == self.children_perm,
            node.tree_level == self.tree_level,
            node.slot_index == self.slot_index,
    {
        NodeOwner {
            meta_own: self.meta_own,
            frame_permission: permission,
            children_perm: self.children_perm,
            tree_level: self.tree_level,
            slot_index: self.slot_index,
        }
    }
}

/// Linear structural resources and PTE owners for one physical page-table
/// node.  Metadata permission intentionally lives outside this record.
pub tracked struct FlatNodeRecord<C: PageTableConfig> {
    pub node: FlatNodeOwner<C>,
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
        &&& forall|i: int|
            0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] self.entries[i];
                let pte = self.node.children_perm.value()[i];
                &&& entry.inv()
                &&& entry.path == self.path.push_tail(i)
                &&& entry.parent_level == self.node.level
                &&& entry.match_pte(pte) || (self.node.level == NR_LEVELS && C::LEADING_BITS_spec()
                    == 0 && entry.borrowed_match_pte(pte))
            }
    }

    pub open spec fn new(
        node: FlatNodeOwner<C>,
        entries: Seq<FlatEntryOwner<C>>,
        path: TreePath<NR_ENTRIES>,
    ) -> Self {
        Self { node, entries, path }
    }

    pub proof fn tracked_new(
        tracked node: FlatNodeOwner<C>,
        tracked entries: Seq<FlatEntryOwner<C>>,
        path: TreePath<NR_ENTRIES>,
    ) -> (tracked result: Self)
        returns
            Self::new(node, entries, path),
    {
        Self { node, entries, path }
    }

    pub open spec fn set_entry(self, idx: int, entry: FlatEntryOwner<C>) -> Self
        recommends
            0 <= idx < self.entries.len(),
    {
        Self { entries: self.entries.update(idx, entry), ..self }
    }

    pub proof fn tracked_borrow_entry<'a>(tracked &'a self, idx: int) -> (tracked entry:
        &'a FlatEntryOwner<C>)
        requires
            0 <= idx < self.entries.len(),
        ensures
            *entry == self.entries[idx],
    {
        self.entries.tracked_borrow(idx)
    }

    pub proof fn tracked_borrow_entry_mut<'a>(tracked &'a mut self, idx: int) -> (tracked entry:
        &'a mut FlatEntryOwner<C>)
        requires
            0 <= idx < old(self).entries.len(),
        ensures
            *entry == old(self).entries[idx],
            *final(self) == old(self).set_entry(idx, *final(entry)),
    {
        self.entries.tracked_borrow_mut(idx)
    }

    pub proof fn tracked_set_entry(tracked &mut self, idx: int, tracked entry: FlatEntryOwner<C>)
        requires
            0 <= idx < old(self).entries.len(),
        ensures
            *final(self) == old(self).set_entry(idx, entry),
    {
        let tracked slot = self.entries.tracked_borrow_mut(idx);
        *slot = entry;
    }
}

/// Flat authoritative ownership of one page table.
pub tracked struct FlatPageTableOwner<C: PageTableConfig> {
    pub ghost root: Paddr,
    pub nodes: Map<Paddr, FlatNodeRecord<C>>,
    /// Full metadata permissions parked for nodes currently held raw in PTEs.
    /// The root is deliberately absent: its live `Frame` owns that permission.
    pub raw_node_permissions: Map<Paddr, FracMetadataPerm>,
}

/// Stable borrow of a raw node.  The two references originate from separate
/// maps, so clients can inspect structural ownership without moving either
/// resource.
pub tracked struct FlatRawNodeRef<'a, C: PageTableConfig> {
    pub record: &'a FlatNodeRecord<C>,
    pub permission: &'a FracMetadataPerm,
}

/// Mutable structural access paired with an immutable, stable metadata
/// permission.  Guard creation borrows `permission`; node operations mutate
/// only `record`.
pub tracked struct FlatRawNodeMut<'a, C: PageTableConfig> {
    pub record: &'a mut FlatNodeRecord<C>,
    pub permission: &'a FracMetadataPerm,
}

/// The not-yet-leased portion of the two authoritative resource maps.
///
/// This value is consumed when one node is leased.  The returned remainder
/// retains the original lifetime, so a cursor can repeatedly split disjoint
/// nodes while previously returned leases stay alive.
pub tracked struct FlatOwnerPartition<'a, C: PageTableConfig> {
    pub nodes: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub permissions: &'a mut Map<Paddr, FracMetadataPerm>,
}

/// Resources for one raw page-table node split out of a flat partition.
/// `permission` may be borrowed for the lifetime of a `FrameRef`, while
/// `record` remains independently mutable for PTE and metadata bookkeeping.
pub tracked struct FlatRawNodeLease<'a, C: PageTableConfig> {
    pub ghost paddr: Paddr,
    pub record: &'a mut FlatNodeRecord<C>,
    pub permission: &'a FracMetadataPerm,
}

impl<'a, C: PageTableConfig> FlatOwnerPartition<'a, C> {
    pub open spec fn contains_raw_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr) && self.permissions.contains_key(paddr)
    }

    /// Splits one raw node out of the partition.  Unlike borrowing directly
    /// from the full maps, this freezes only the selected slots; `remainder`
    /// can still be mutated or split again while `lease` is alive.
    pub proof fn tracked_lease_raw_node(
        tracked self,
        paddr: Paddr,
    ) -> (tracked (lease, remainder): (
        FlatRawNodeLease<'a, C>,
        FlatOwnerPartition<'a, C>,
    ))
        requires self.contains_raw_node(paddr),
        ensures
            lease.paddr == paddr,
            *lease.record == (*old(self.nodes))[paddr],
            *lease.permission == (*old(self.permissions))[paddr],
            *remainder.nodes == old(self.nodes).remove_keys(set![paddr]),
            *remainder.permissions == old(self.permissions).remove_keys(set![paddr]),
    {
        let ghost key = set![paddr];
        let tracked (node_slot, nodes) = self.nodes.tracked_borrow_mut_split(key);
        let tracked (permission_slot, permissions) = self
            .permissions
            .tracked_borrow_mut_split(key);
        let tracked record = node_slot.tracked_borrow_mut(paddr);
        let tracked permission = permission_slot.tracked_borrow(paddr);
        (
            FlatRawNodeLease { paddr, record, permission },
            FlatOwnerPartition { nodes, permissions },
        )
    }

    pub proof fn tracked_insert_raw_node(
        tracked &mut self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    )
        requires
            !old(self).nodes.contains_key(paddr),
            !old(self).permissions.contains_key(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
        ensures
            *final(self).nodes == old(self).nodes.insert(paddr, record),
            *final(self).permissions == old(self).permissions.insert(paddr, permission),
    {
        self.nodes.tracked_insert(paddr, record);
        self.permissions.tracked_insert(paddr, permission);
    }
}

impl<C: PageTableConfig> FlatPageTableOwner<C> {
    pub open spec fn new(root: Paddr, record: FlatNodeRecord<C>) -> Self {
        Self { root, nodes: Map::empty().insert(root, record), raw_node_permissions: Map::empty() }
    }

    pub proof fn tracked_new(root: Paddr, tracked record: FlatNodeRecord<C>) -> (tracked result:
        Self)
        returns
            Self::new(root, record),
    {
        let tracked mut nodes = Map::tracked_empty();
        nodes.tracked_insert(root, record);
        Self { root, nodes, raw_node_permissions: Map::tracked_empty() }
    }

    pub open spec fn contains_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr)
    }

    pub open spec fn node(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends
            self.contains_node(paddr),
    {
        self.nodes[paddr]
    }

    pub open spec fn local_node_inv(self, paddr: Paddr) -> bool {
        &&& self.contains_node(paddr)
        &&& self.node(paddr).paddr() == paddr
        &&& self.node(paddr).local_inv()
        &&& forall|i: int|
            0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] self.node(paddr).entries[i];
                entry.is_node() ==> {
                    &&& self.contains_node(entry.child_paddr())
                    &&& self.raw_node_permissions.contains_key(entry.child_paddr())
                    &&& self.node(entry.child_paddr()).path == entry.path
                    &&& self.node(entry.child_paddr()).node.level + 1 == self.node(paddr).node.level
                }
            }
    }

    /// Paging level decreases on every node edge, bounding recursion.
    pub open spec fn subtree_inv_at(self, paddr: Paddr, depth: nat) -> bool
        decreases depth,
    {
        &&& self.local_node_inv(paddr)
        &&& self.node(paddr).node.level == depth
        &&& if depth == 0 {
            false
        } else {
            forall|i: int|
                0 <= i < NR_ENTRIES ==> {
                    let entry = #[trigger] self.node(paddr).entries[i];
                    entry.is_node() ==> self.subtree_inv_at(entry.child_paddr(), (depth - 1) as nat)
                }
        }
    }

    pub open spec fn reachable_from(self, from: Paddr, target: Paddr, depth: nat) -> bool
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
            self.contains_node(parent1) && self.contains_node(parent2) && 0 <= i < NR_ENTRIES && 0
                <= j < NR_ENTRIES && (#[trigger] self.node(parent1).entries[i]).is_node() && (
            #[trigger] self.node(parent2).entries[j]).is_node() && self.node(
                parent1,
            ).entries[i].child_paddr() == self.node(parent2).entries[j].child_paddr() ==> parent1
                == parent2 && i == j
    }

    pub open spec fn root_has_no_parent(self) -> bool {
        forall|parent: Paddr, i: int|
            self.contains_node(parent) && 0 <= i < NR_ENTRIES && (#[trigger] self.node(
                parent,
            ).entries[i]).is_node() ==> self.node(parent).entries[i].child_paddr() != self.root
    }

    pub open spec fn all_nodes_reachable(self) -> bool {
        forall|paddr: Paddr| #[trigger]
            self.contains_node(paddr) ==> self.reachable_from(self.root, paddr, NR_LEVELS as nat)
    }

    pub open spec fn subtree_nodes(self, root: Paddr) -> Set<Paddr> {
        self.nodes.dom().filter(|paddr: Paddr| self.reachable_from(root, paddr, NR_LEVELS as nat))
    }

    pub open spec fn inv(self) -> bool {
        &&& self.contains_node(self.root)
        &&& self.raw_node_permissions.dom() == self.nodes.dom().remove(self.root)
        &&& forall|paddr: Paddr| #[trigger]
            self.raw_node_permissions.contains_key(paddr)
                ==> self.raw_node_permissions[paddr].frac() == 1
        &&& self.node(self.root).path == TreePath::<NR_ENTRIES>::new(Seq::empty())
        &&& self.subtree_inv_at(self.root, NR_LEVELS as nat)
        &&& self.unique_parent()
        &&& self.root_has_no_parent()
        &&& self.all_nodes_reachable()
    }

    pub proof fn tracked_borrow_node<'a>(tracked &'a self, paddr: Paddr) -> (tracked node:
        &'a FlatNodeRecord<C>)
        requires
            self.contains_node(paddr),
        ensures
            *node == self.node(paddr),
    {
        self.nodes.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_entry<'a>(
        tracked &'a self,
        paddr: Paddr,
        idx: int,
    ) -> (tracked entry: &'a FlatEntryOwner<C>)
        requires
            self.contains_node(paddr),
            0 <= idx < self.node(paddr).entries.len(),
        ensures
            *entry == self.node(paddr).entries[idx],
    {
        self.nodes.tracked_borrow(paddr).tracked_borrow_entry(idx)
    }

    pub proof fn tracked_borrow_raw_node_permission<'a>(
        tracked &'a self,
        paddr: Paddr,
    ) -> (tracked permission: &'a FracMetadataPerm)
        requires
            self.raw_node_permissions.contains_key(paddr),
        ensures
            *permission == self.raw_node_permissions[paddr],
    {
        self.raw_node_permissions.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_raw_node<'a>(tracked &'a self, paddr: Paddr) -> (tracked raw_node:
        FlatRawNodeRef<'a, C>)
        requires
            self.contains_node(paddr),
            self.raw_node_permissions.contains_key(paddr),
        ensures
            *raw_node.record == self.node(paddr),
            *raw_node.permission == self.raw_node_permissions[paddr],
    {
        let tracked record = self.nodes.tracked_borrow(paddr);
        let tracked permission = self.raw_node_permissions.tracked_borrow(paddr);
        FlatRawNodeRef { record, permission }
    }

    pub proof fn tracked_borrow_raw_node_mut<'a>(
        tracked &'a mut self,
        paddr: Paddr,
    ) -> (tracked raw_node: FlatRawNodeMut<'a, C>)
        requires
            old(self).contains_node(paddr),
            old(self).raw_node_permissions.contains_key(paddr),
        ensures
            *raw_node.record == old(self).node(paddr),
            *raw_node.permission == old(self).raw_node_permissions[paddr],
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(paddr, *final(raw_node.record)),
            final(self).raw_node_permissions == old(self).raw_node_permissions,
    {
        let tracked record = self.nodes.tracked_borrow_mut(paddr);
        let tracked permission = self.raw_node_permissions.tracked_borrow(paddr);
        FlatRawNodeMut { record, permission }
    }

    /// Borrows both authoritative maps as a consumable partition.  Leases
    /// produced from this partition are disjoint and do not move their
    /// `FlatNodeRecord`s.
    pub proof fn tracked_partition<'a>(
        tracked &'a mut self,
    ) -> (tracked partition: FlatOwnerPartition<'a, C>)
        ensures
            *partition.nodes == old(self).nodes,
            *partition.permissions == old(self).raw_node_permissions,
            final(self).root == old(self).root,
            final(self).nodes == *final(partition.nodes),
            final(self).raw_node_permissions == *final(partition.permissions),
    {
        FlatOwnerPartition {
            nodes: &mut self.nodes,
            permissions: &mut self.raw_node_permissions,
        }
    }

    pub proof fn tracked_borrow_subtree<'a>(tracked &'a self, root: Paddr) -> (tracked subtree:
        FlatOwnerSubtree<'a, C>)
        requires
            self.contains_node(root),
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
        requires
            old(self).contains_node(root),
        ensures
            subtree.root == root,
            *subtree.nodes == old(self).nodes.restrict(old(self).subtree_nodes(root)),
            *subtree.remainder == old(self).nodes.remove_keys(old(self).subtree_nodes(root)),
            *subtree.permissions == old(self).raw_node_permissions.restrict(
                old(self).subtree_nodes(root).remove(old(self).root),
            ),
            *subtree.permission_remainder == old(self).raw_node_permissions.remove_keys(
                old(self).subtree_nodes(root).remove(old(self).root),
            ),
    {
        let ghost keys = self.subtree_nodes(root);
        assert(keys <= self.nodes.dom());
        let ghost permission_keys = keys.remove(self.root);
        assert(permission_keys <= self.raw_node_permissions.dom());
        let tracked (nodes, remainder) = self.nodes.tracked_borrow_mut_split(keys);
        let tracked (permissions, permission_remainder) =
            self.raw_node_permissions.tracked_borrow_mut_split(permission_keys);
        FlatOwnerSubtreeMut { nodes, remainder, permissions, permission_remainder, root }
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

    /// Inserts a node that has just been converted from an owned `Frame` into
    /// a raw child PTE.  The permission transfer is atomic at the model level.
    pub proof fn tracked_insert_raw_node(
        tracked &mut self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    )
        requires
            !old(self).contains_node(paddr),
            !old(self).raw_node_permissions.contains_key(paddr),
            paddr != old(self).root,
            record.paddr() == paddr,
            permission.frac() == 1,
        ensures
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(paddr, record),
            final(self).raw_node_permissions == old(self).raw_node_permissions.insert(
                paddr,
                permission,
            ),
    {
        self.nodes.tracked_insert(paddr, record);
        self.raw_node_permissions.tracked_insert(paddr, permission);
    }

    /// Installs a detached node under `parent[idx]`.  Only one entry in the
    /// parent record and two flat-map slots change; no ancestor or sibling
    /// owner is taken out and reinserted.
    pub proof fn tracked_attach_raw_child(
        tracked &mut self,
        parent: Paddr,
        idx: int,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    )
        requires
            old(self).contains_node(parent),
            0 <= idx < old(self).node(parent).entries.len(),
            old(self).node(parent).entries[idx].is_absent(),
            !old(self).contains_node(record.paddr()),
            !old(self).raw_node_permissions.contains_key(record.paddr()),
            record.paddr() != old(self).root,
            permission.frac() == 1,
        ensures
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(
                parent,
                old(self).node(parent).set_entry(
                    idx,
                    FlatEntryOwner::new_node(
                        record.paddr(),
                        old(self).node(parent).entries[idx].path,
                        old(self).node(parent).entries[idx].parent_level,
                    ),
                ),
            ).insert(record.paddr(), record),
            final(self).raw_node_permissions == old(self).raw_node_permissions.insert(
                record.paddr(),
                permission,
            ),
    {
        let ghost child = record.paddr();
        let ghost old_entry = self.node(parent).entries[idx];
        let tracked edge = FlatEntryOwner::tracked_new_node(
            child,
            old_entry.path,
            old_entry.parent_level,
        );
        {
            let tracked parent_record = self.nodes.tracked_borrow_mut(parent);
            parent_record.tracked_set_entry(idx, edge);
        }
        self.nodes.tracked_insert(child, record);
        self.raw_node_permissions.tracked_insert(child, permission);
    }

    pub proof fn tracked_remove_node(tracked &mut self, paddr: Paddr) -> (tracked record:
        FlatNodeRecord<C>)
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

    /// Removes a raw child node and returns both resources needed to rebuild
    /// an owning `Frame` handle.
    pub proof fn tracked_remove_raw_node(tracked &mut self, paddr: Paddr) -> (tracked (
        record,
        permission,
    ): (FlatNodeRecord<C>, FracMetadataPerm))
        requires
            old(self).contains_node(paddr),
            old(self).raw_node_permissions.contains_key(paddr),
            paddr != old(self).root,
        ensures
            record == old(self).node(paddr),
            permission == old(self).raw_node_permissions[paddr],
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.remove(paddr),
            final(self).raw_node_permissions == old(self).raw_node_permissions.remove(paddr),
    {
        let tracked record = self.nodes.tracked_remove(paddr);
        let tracked permission = self.raw_node_permissions.tracked_remove(paddr);
        (record, permission)
    }

    /// Detaches `parent[idx]` and returns the child resources that an owning
    /// `Frame` reconstruction needs.  This is the inverse ownership transfer
    /// of `tracked_attach_raw_child`.
    pub proof fn tracked_detach_raw_child(tracked &mut self, parent: Paddr, idx: int) -> (tracked (
        record,
        permission,
    ): (FlatNodeRecord<C>, FracMetadataPerm))
        requires
            old(self).contains_node(parent),
            0 <= idx < old(self).node(parent).entries.len(),
            old(self).node(parent).entries[idx].is_node(),
            old(self).contains_node(old(self).node(parent).entries[idx].child_paddr()),
            old(self).raw_node_permissions.contains_key(
                old(self).node(parent).entries[idx].child_paddr(),
            ),
            old(self).node(parent).entries[idx].child_paddr() != old(self).root,
        ensures
            record == old(self).node(old(self).node(parent).entries[idx].child_paddr()),
            permission == old(self).raw_node_permissions[old(self).node(
                parent,
            ).entries[idx].child_paddr()],
            final(self).root == old(self).root,
            final(self).nodes == old(self).nodes.insert(
                parent,
                old(self).node(parent).set_entry(
                    idx,
                    FlatEntryOwner::new_absent(
                        old(self).node(parent).entries[idx].path,
                        old(self).node(parent).entries[idx].parent_level,
                    ),
                ),
            ).remove(old(self).node(parent).entries[idx].child_paddr()),
            final(self).raw_node_permissions == old(self).raw_node_permissions.remove(
                old(self).node(parent).entries[idx].child_paddr(),
            ),
    {
        let ghost old_entry = self.node(parent).entries[idx];
        let ghost child = old_entry.child_paddr();
        let tracked absent = FlatEntryOwner::tracked_new_absent(
            old_entry.path,
            old_entry.parent_level,
        );
        {
            let tracked parent_record = self.nodes.tracked_borrow_mut(parent);
            parent_record.tracked_set_entry(idx, absent);
        }
        let tracked record = self.nodes.tracked_remove(child);
        let tracked permission = self.raw_node_permissions.tracked_remove(child);
        (record, permission)
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
        recommends
            self.inv(),
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

    pub proof fn tracked_borrow_record(tracked &self) -> (tracked record: &'a FlatNodeRecord<C>)
        requires
            self.inv(),
        ensures
            *record == self.record(),
    {
        self.owner.nodes.tracked_borrow(self.root)
    }

    pub proof fn tracked_borrow_entry(tracked &self, idx: int) -> (tracked entry:
        &'a FlatEntryOwner<C>)
        requires
            self.inv(),
            0 <= idx < self.record().entries.len(),
        ensures
            *entry == self.entry(idx),
    {
        self.owner.nodes.tracked_borrow(self.root).tracked_borrow_entry(idx)
    }

    pub proof fn tracked_child(tracked &self, idx: int) -> (tracked child: FlatOwnerSubtree<'a, C>)
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

    pub proof fn tracked_borrow_raw_root(tracked &self) -> (tracked raw_node: FlatRawNodeRef<'a, C>)
        requires
            self.inv(),
            self.root != self.owner.root,
            self.owner.raw_node_permissions.contains_key(self.root),
        ensures
            *raw_node.record == self.owner.node(self.root),
            *raw_node.permission == self.owner.raw_node_permissions[self.root],
    {
        self.owner.tracked_borrow_raw_node(self.root)
    }
}

/// Mutable borrow of a subtree and the disjoint complement of its node map.
pub tracked struct FlatOwnerSubtreeMut<'a, C: PageTableConfig> {
    pub nodes: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub remainder: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub permissions: &'a mut Map<Paddr, FracMetadataPerm>,
    pub permission_remainder: &'a mut Map<Paddr, FracMetadataPerm>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatOwnerSubtreeMut<'a, C> {
    pub open spec fn contains_node(self, paddr: Paddr) -> bool {
        self.nodes.contains_key(paddr)
    }

    pub open spec fn record(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends
            self.contains_node(paddr),
    {
        self.nodes[paddr]
    }

    pub proof fn tracked_borrow_node(tracked &self, paddr: Paddr) -> (tracked node: &FlatNodeRecord<
        C,
    >)
        requires
            self.contains_node(paddr),
        ensures
            *node == self.record(paddr),
    {
        self.nodes.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_node_mut(tracked &mut self, paddr: Paddr) -> (tracked node:
        &mut FlatNodeRecord<C>)
        requires
            old(self).contains_node(paddr),
        ensures
            *node == old(self).record(paddr),
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).nodes == old(self).nodes.insert(paddr, *final(node)),
    {
        self.nodes.tracked_borrow_mut(paddr)
    }

    pub proof fn tracked_borrow_entry(tracked &self, paddr: Paddr, idx: int) -> (tracked entry:
        &FlatEntryOwner<C>)
        requires
            self.contains_node(paddr),
            0 <= idx < self.record(paddr).entries.len(),
        ensures
            *entry == self.record(paddr).entries[idx],
    {
        self.nodes.tracked_borrow(paddr).tracked_borrow_entry(idx)
    }

    pub proof fn tracked_borrow_entry_mut(
        tracked &mut self,
        paddr: Paddr,
        idx: int,
    ) -> (tracked entry: &mut FlatEntryOwner<C>)
        requires
            old(self).contains_node(paddr),
            0 <= idx < old(self).record(paddr).entries.len(),
        ensures
            *entry == old(self).record(paddr).entries[idx],
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).permissions == *old(self).permissions,
            *final(self).permission_remainder == *old(self).permission_remainder,
            *final(self).nodes == old(self).nodes.insert(
                paddr,
                old(self).record(paddr).set_entry(idx, *final(entry)),
            ),
    {
        self.nodes.tracked_borrow_mut(paddr).tracked_borrow_entry_mut(idx)
    }

    pub proof fn tracked_borrow_raw_node_permission(
        tracked &self,
        paddr: Paddr,
    ) -> (tracked permission: &FracMetadataPerm)
        requires
            self.permissions.contains_key(paddr),
        ensures
            *permission == (*old(self.permissions))[paddr],
    {
        self.permissions.tracked_borrow(paddr)
    }

    pub proof fn tracked_borrow_raw_node_mut<'b>(
        tracked &'b mut self,
        paddr: Paddr,
    ) -> (tracked raw_node: FlatRawNodeMut<'b, C>)
        requires
            old(self).contains_node(paddr),
            old(self).permissions.contains_key(paddr),
        ensures
            *raw_node.record == old(self).record(paddr),
            *raw_node.permission == (*old(self.permissions))[paddr],
            final(self).root == old(self).root,
            *final(self).remainder == *old(self).remainder,
            *final(self).permission_remainder == *old(self).permission_remainder,
            *final(self).nodes == old(self).nodes.insert(paddr, *final(raw_node.record)),
            *final(self).permissions == *old(self).permissions,
    {
        let tracked record = self.nodes.tracked_borrow_mut(paddr);
        let tracked permission = self.permissions.tracked_borrow(paddr);
        FlatRawNodeMut { record, permission }
    }
}

} // verus!
