//! Flat ownership model for page tables.
//!
//! The model does not recursively own child node resources. A node entry
//! records only the physical address of its child;
//! the corresponding linear resources live in `FlatPageTableOwner::nodes`.
use vstd::prelude::*;
use vstd_extra::{array_ptr, ghost_tree::TreePath, ownership::*};

use crate::mm::frame::meta::{META_SLOT_SIZE, mapping::meta_to_frame};
use crate::mm::kspace::{FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR};
use crate::mm::page_table::{PageTableConfig, PageTableEntryTrait, PageTableGuard};
use crate::mm::{Paddr, PagingLevel, Vaddr, paddr_to_vaddr, page_size};
use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS, valid_frame_paddr};
use crate::specs::mm::frame::mapping::{index_to_meta, max_meta_slots};
use crate::specs::mm::frame::meta_owners::FracMetadataPerm;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::node::entry_owners::FrameEntryOwner;
use crate::specs::mm::page_table::node::owners::PageMetaOwner;
use crate::specs::mm::page_table::owners::INC_LEVELS;

verus! {

/// Ownership of one PTE in the flat model. The node variant deliberately
/// contains only an address; its structural resources are stored in the node
/// map.
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
    pub open spec fn new(
        meta_own: PageMetaOwner,
        children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
        level: PagingLevel,
        tree_level: int,
        slot_index: int,
    ) -> Self {
        Self { meta_own, children_perm, level, tree_level, slot_index }
    }

    pub proof fn tracked_new(
        tracked meta_own: PageMetaOwner,
        tracked children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
        level: PagingLevel,
        tree_level: int,
        slot_index: int,
    ) -> (tracked result: Self)
        returns
            Self::new(meta_own, children_perm, level, tree_level, slot_index),
    {
        Self { meta_own, children_perm, level, tree_level, slot_index }
    }

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

    /// Structural result of allocating a zero-filled page-table node.
    /// `path` is supplied by the caller, so a fresh node never needs the old
    /// recursive-tree "allocate at empty path, then rebase children" dance.
    pub open spec fn allocated_empty(self, level: PagingLevel, path: TreePath<NR_ENTRIES>) -> bool {
        &&& self.node.inv()
        &&& self.node.level == level
        &&& self.node.tree_level == INC_LEVELS - level - 1
        &&& self.path == path
        &&& self.entries.len() == NR_ENTRIES
        &&& forall|i: int| 0 <= i < NR_ENTRIES ==> {
            let entry = #[trigger] self.entries[i];
            &&& entry.is_absent()
            &&& entry.inv()
            &&& entry.path == path.push_tail(i)
            &&& entry.parent_level == level
            &&& self.node.children_perm.value()[i] == C::E::new_absent_spec()
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

    proof fn tracked_new_absent_entries(
        path: TreePath<NR_ENTRIES>,
        parent_level: PagingLevel,
        len: nat,
    ) -> (tracked entries: Seq<FlatEntryOwner<C>>)
        ensures
            entries.len() == len,
            forall|i: int| 0 <= i < len ==> {
                let entry = #[trigger] entries[i];
                &&& entry.is_absent()
                &&& entry.path == path.push_tail(i)
                &&& entry.parent_level == parent_level
            },
        decreases len,
    {
        if len == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut entries = Self::tracked_new_absent_entries(
                path,
                parent_level,
                (len - 1) as nat,
            );
            let tracked entry = FlatEntryOwner::tracked_new_absent(
                path.push_tail((len - 1) as int),
                parent_level,
            );
            entries.tracked_push(entry);
            entries
        }
    }

    /// Builds the structural record returned by page-table-node allocation.
    /// No recursive owner is created: all PTE slots are represented directly
    /// in this record, and the frame metadata permission remains separate.
    pub proof fn tracked_new_empty(
        tracked node: FlatNodeOwner<C>,
        path: TreePath<NR_ENTRIES>,
    ) -> (tracked result: Self)
        ensures
            result.node == node,
            result.path == path,
            result.entries.len() == NR_ENTRIES,
            forall|i: int| 0 <= i < NR_ENTRIES ==> {
                let entry = #[trigger] result.entries[i];
                &&& entry.is_absent()
                &&& entry.path == path.push_tail(i)
                &&& entry.parent_level == node.level
            },
    {
        let ghost parent_level = node.level;
        let tracked entries = Self::tracked_new_absent_entries(
            path,
            parent_level,
            NR_ENTRIES as nat,
        );
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

/// Structural lease for the root node.  Its metadata permission remains in
/// the live root `Frame`, so unlike a raw child lease this contains no
/// `FracMetadataPerm`.
pub tracked struct FlatRootNodeLease<'a, C: PageTableConfig> {
    pub ghost paddr: Paddr,
    pub record: &'a mut FlatNodeRecord<C>,
}

/// Cursor-local ownership of raw nodes.
///
/// A node moves from `remainder` to `leases` at most once.  Moving the lease
/// value itself is harmless: both references still point into the stable flat
/// maps, so a `FrameRef<'a, _>` can keep borrowing its metadata permission
/// while the cursor mutates other, disjoint node records.
pub tracked struct FlatCursorResources<'a, C: PageTableConfig> {
    pub root: FlatRootNodeLease<'a, C>,
    pub remainder: FlatOwnerPartition<'a, C>,
    pub leases: Map<Paddr, FlatRawNodeLease<'a, C>>,
}

/// One level of a flat cursor path.  It identifies the node by physical
/// address; ownership of the node itself remains in `FlatCursorResources`.
pub ghost struct FlatCursorContinuation<'rcu, C: PageTableConfig> {
    pub ghost node: Paddr,
    pub ghost idx: usize,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost level: PagingLevel,
    pub ghost guard: PageTableGuard<'rcu, C>,
}

/// Cursor ownership after the recursive tree has been removed.
///
/// `continuations` contains navigation state only.  Linear node resources and
/// raw metadata permissions are addressed through `resources` by paddr.
pub tracked struct FlatCursorOwner<'a, 'rcu, C: PageTableConfig> {
    pub resources: FlatCursorResources<'a, C>,
    pub ghost continuations: Map<int, FlatCursorContinuation<'rcu, C>>,
    pub ghost root: Paddr,
    pub ghost level: PagingLevel,
    pub ghost guard_level: PagingLevel,
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

    /// Inserts a freshly converted raw node and immediately splits it out as
    /// a stable lease.  Allocation paths need this combined operation: the
    /// returned `PageTableNodeRef` borrows the permission for `'a`, while the
    /// remainder must stay available for later cursor descents/allocations.
    pub proof fn tracked_insert_and_lease_raw_node(
        tracked self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked (lease, remainder): (
        FlatRawNodeLease<'a, C>,
        FlatOwnerPartition<'a, C>,
    ))
        requires
            !self.nodes.contains_key(paddr),
            !self.permissions.contains_key(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
        ensures
            lease.paddr == paddr,
            *lease.record == record,
            *lease.permission == permission,
            *remainder.nodes == *old(self.nodes),
            *remainder.permissions == *old(self.permissions),
    {
        self.nodes.tracked_insert(paddr, record);
        self.permissions.tracked_insert(paddr, permission);
        self.tracked_lease_raw_node(paddr)
    }
}

impl<'a, C: PageTableConfig> FlatRawNodeLease<'a, C> {
    pub open spec fn node(self) -> FlatNodeOwner<C> {
        self.record.node
    }

    pub open spec fn entry(self, idx: int) -> FlatEntryOwner<C>
        recommends
            0 <= idx < self.record.entries.len(),
    {
        self.record.entries[idx]
    }

    pub proof fn tracked_borrow_entry(tracked &self, idx: int) -> (tracked entry:
        &FlatEntryOwner<C>)
        requires
            0 <= idx < self.record.entries.len(),
        ensures
            *entry == self.entry(idx),
    {
        self.record.tracked_borrow_entry(idx)
    }

    pub proof fn tracked_borrow_entry_mut(tracked &mut self, idx: int) -> (tracked entry:
        &mut FlatEntryOwner<C>)
        requires
            0 <= idx < old(self).record.entries.len(),
        ensures
            *entry == old(self).entry(idx),
            final(self).paddr == old(self).paddr,
            *final(self).permission == *old(self).permission,
            *final(self).record == old(self).record.set_entry(idx, *final(entry)),
    {
        self.record.tracked_borrow_entry_mut(idx)
    }
}

impl<'a, C: PageTableConfig> FlatCursorResources<'a, C> {
    pub open spec fn contains_leased(self, paddr: Paddr) -> bool {
        self.root.paddr == paddr || self.leases.contains_key(paddr)
    }

    pub open spec fn contains_raw_leased(self, paddr: Paddr) -> bool {
        self.leases.contains_key(paddr)
    }

    pub open spec fn contains_unleased(self, paddr: Paddr) -> bool {
        self.remainder.contains_raw_node(paddr)
    }

    pub proof fn tracked_new(
        tracked remainder: FlatOwnerPartition<'a, C>,
        root: Paddr,
    ) -> (tracked result: Self)
        requires
            remainder.nodes.contains_key(root),
            !remainder.permissions.contains_key(root),
        ensures
            result.root.paddr == root,
            *result.root.record == (*old(remainder.nodes))[root],
            result.leases =~= Map::empty(),
            *result.remainder.nodes == old(remainder.nodes).remove_keys(set![root]),
            *result.remainder.permissions == *old(remainder.permissions),
    {
        let tracked FlatOwnerPartition { nodes, permissions } = remainder;
        let tracked (root_slot, nodes) = nodes.tracked_borrow_mut_split(set![root]);
        let tracked record = root_slot.tracked_borrow_mut(root);
        Self {
            root: FlatRootNodeLease { paddr: root, record },
            remainder: FlatOwnerPartition { nodes, permissions },
            leases: Map::tracked_empty(),
        }
    }

    /// Leases a node on first visit.  Already leased nodes are looked up by
    /// paddr through `tracked_borrow_permission`/`tracked_borrow_record_mut`;
    /// they are never removed and reinserted while cursor guards are alive.
    pub proof fn tracked_lease_node(tracked self, paddr: Paddr) -> (tracked result: Self)
        requires
            self.contains_unleased(paddr),
            !self.contains_leased(paddr),
        ensures
            result.contains_leased(paddr),
            result.leases.dom() == self.leases.dom().insert(paddr),
            *result.remainder.nodes == old(self.remainder.nodes).remove_keys(set![paddr]),
            *result.remainder.permissions == old(self.remainder.permissions).remove_keys(
                set![paddr],
            ),
    {
        let tracked Self { root, remainder, mut leases } = self;
        let tracked (lease, remainder) = remainder.tracked_lease_raw_node(paddr);
        leases.tracked_insert(paddr, lease);
        Self { root, remainder, leases }
    }

    /// Parks a newly allocated node's metadata permission in the flat store
    /// and retains a lease for the guard returned by the allocation path.
    pub proof fn tracked_insert_and_lease_node(
        tracked self,
        paddr: Paddr,
        tracked record: FlatNodeRecord<C>,
        tracked permission: FracMetadataPerm,
    ) -> (tracked result: Self)
        requires
            !self.contains_leased(paddr),
            !self.contains_unleased(paddr),
            record.paddr() == paddr,
            permission.frac() == 1,
        ensures
            result.contains_leased(paddr),
            result.leases.dom() == self.leases.dom().insert(paddr),
            *result.remainder.nodes == *old(self.remainder.nodes),
            *result.remainder.permissions == *old(self.remainder.permissions),
    {
        let tracked Self { root, remainder, mut leases } = self;
        let tracked (lease, remainder) = remainder.tracked_insert_and_lease_raw_node(
            paddr,
            record,
            permission,
        );
        leases.tracked_insert(paddr, lease);
        Self { root, remainder, leases }
    }

    pub proof fn tracked_borrow_permission(
        tracked &self,
        paddr: Paddr,
    ) -> (tracked permission: &'a FracMetadataPerm)
        requires
            self.contains_raw_leased(paddr),
        ensures
            *permission == *self.leases[paddr].permission,
    {
        let tracked lease = self.leases.tracked_borrow(paddr);
        lease.permission
    }

    pub open spec fn leased_record(self, paddr: Paddr) -> FlatNodeRecord<C>
        recommends
            self.contains_leased(paddr),
    {
        if self.root.paddr == paddr {
            *self.root.record
        } else {
            *self.leases[paddr].record
        }
    }

    pub proof fn tracked_borrow_record_mut<'b>(
        tracked &'b mut self,
        paddr: Paddr,
    ) -> (tracked record: &'b mut FlatNodeRecord<C>)
        requires
            old(self).contains_leased(paddr),
        ensures
            *record == old(self).leased_record(paddr),
            final(self).leases.dom() == old(self).leases.dom(),
            *final(self).remainder.nodes == *old(self).remainder.nodes,
            *final(self).remainder.permissions == *old(self).remainder.permissions,
    {
        if self.root.paddr == paddr {
            &mut *self.root.record
        } else {
            let tracked lease = self.leases.tracked_borrow_mut(paddr);
            &mut *lease.record
        }
    }
}

impl<'rcu, C: PageTableConfig> FlatCursorContinuation<'rcu, C> {
    pub open spec fn new(
        node: Paddr,
        idx: usize,
        path: TreePath<NR_ENTRIES>,
        level: PagingLevel,
        guard: PageTableGuard<'rcu, C>,
    ) -> Self {
        Self { node, idx, path, level, guard }
    }
}

impl<'a, 'rcu, C: PageTableConfig> FlatCursorOwner<'a, 'rcu, C> {
    pub open spec fn current(self) -> FlatCursorContinuation<'rcu, C>
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        self.continuations[self.level - 1]
    }

    pub open spec fn current_paddr(self) -> Paddr
        recommends
            self.continuations.contains_key(self.level - 1),
    {
        self.current().node
    }

    pub proof fn tracked_new(
        tracked resources: FlatCursorResources<'a, C>,
        root: Paddr,
        idx: usize,
        path: TreePath<NR_ENTRIES>,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked result: Self)
        requires
            resources.root.paddr == root,
            resources.root.record.node.level == NR_LEVELS,
            resources.root.record.path == path,
            idx < NR_ENTRIES,
        ensures
            result.root == root,
            result.level == NR_LEVELS,
            result.guard_level == NR_LEVELS,
            result.continuations.dom() == set![(NR_LEVELS - 1) as int],
            result.continuations[(NR_LEVELS - 1) as int].node == root,
            result.continuations[(NR_LEVELS - 1) as int].idx == idx,
            result.continuations[(NR_LEVELS - 1) as int].path == path,
    {
        let ghost root_cont = FlatCursorContinuation::new(
            root,
            idx,
            path,
            NR_LEVELS as PagingLevel,
            guard,
        );
        let ghost continuations = Map::empty().insert((NR_LEVELS - 1) as int, root_cont);
        Self {
            resources,
            continuations,
            root,
            level: NR_LEVELS as PagingLevel,
            guard_level: NR_LEVELS as PagingLevel,
        }
    }

    /// Descends to a raw child without moving either the parent or child node
    /// record.  Only navigation state is inserted into `continuations`.
    pub proof fn tracked_push_child(
        tracked self,
        child: Paddr,
        idx: usize,
        path: TreePath<NR_ENTRIES>,
        child_level: PagingLevel,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked result: Self)
        requires
            self.resources.contains_unleased(child),
            !self.resources.contains_leased(child),
            child_level + 1 == self.level,
        ensures
            result.root == self.root,
            result.level == child_level,
            result.guard_level == self.guard_level,
            result.resources.contains_leased(child),
            result.continuations.contains_key(child_level - 1),
            result.continuations[child_level - 1].node == child,
            result.continuations[child_level - 1].idx == idx,
            result.continuations[child_level - 1].path == path,
    {
        let tracked Self {
            resources,
            continuations,
            root,
            level: _,
            guard_level,
        } = self;
        let tracked resources = resources.tracked_lease_node(child);
        let ghost continuation = FlatCursorContinuation::new(
            child,
            idx,
            path,
            child_level,
            guard,
        );
        let ghost continuations = continuations.insert((child_level - 1) as int, continuation);
        Self { resources, continuations, root, level: child_level, guard_level }
    }

    pub proof fn tracked_borrow_node_permission(
        tracked &self,
        paddr: Paddr,
    ) -> (tracked permission: &'a FracMetadataPerm)
        requires
            self.resources.contains_raw_leased(paddr),
        ensures
            *permission == *self.resources.leases[paddr].permission,
    {
        self.resources.tracked_borrow_permission(paddr)
    }

    pub proof fn tracked_borrow_node_record_mut<'b>(
        tracked &'b mut self,
        paddr: Paddr,
    ) -> (tracked record: &'b mut FlatNodeRecord<C>)
        requires
            old(self).resources.contains_leased(paddr),
        ensures
            *record == *old(self).resources.leases[paddr].record,
            final(self).root == old(self).root,
            final(self).level == old(self).level,
            final(self).guard_level == old(self).guard_level,
            final(self).continuations == old(self).continuations,
    {
        self.resources.tracked_borrow_record_mut(paddr)
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

    /// Starts cursor borrowing directly from the authoritative flat owner.
    /// The root record is split out structurally; only non-root raw nodes can
    /// contribute metadata permissions to later leases.
    pub proof fn tracked_cursor_resources<'a>(
        tracked &'a mut self,
    ) -> (tracked resources: FlatCursorResources<'a, C>)
        requires
            old(self).contains_node(old(self).root),
            !old(self).raw_node_permissions.contains_key(old(self).root),
        ensures
            resources.root.paddr == old(self).root,
            *resources.root.record == old(self).node(old(self).root),
            resources.leases =~= Map::empty(),
            *resources.remainder.nodes == old(self).nodes.remove_keys(set![old(self).root]),
            *resources.remainder.permissions == old(self).raw_node_permissions,
    {
        let ghost root = self.root;
        let tracked partition = self.tracked_partition();
        FlatCursorResources::tracked_new(partition, root)
    }

    pub proof fn tracked_borrow_subtree<'a>(tracked &'a self, root: Paddr) -> (tracked subtree:
        FlatSubtreeRef<'a, C>)
        requires
            self.contains_node(root),
        ensures
            subtree.root == root,
            *subtree.owner == *self,
    {
        FlatSubtreeRef { owner: self, root }
    }

    /// Borrow a subtree by splitting the flat map. No node record is removed
    /// or moved; the complement remains borrowed in `remainder`.
    pub proof fn tracked_borrow_subtree_mut<'a>(
        tracked &'a mut self,
        root: Paddr,
    ) -> (tracked subtree: FlatSubtreeMut<'a, C>)
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
        FlatSubtreeMut { nodes, remainder, permissions, permission_remainder, root }
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
pub tracked struct FlatSubtreeRef<'a, C: PageTableConfig> {
    pub owner: &'a FlatPageTableOwner<C>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatSubtreeRef<'a, C> {
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

    pub proof fn tracked_child(tracked &self, idx: int) -> (tracked child: FlatSubtreeRef<'a, C>)
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
        FlatSubtreeRef { owner: self.owner, root: self.entry(idx).child_paddr() }
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
pub tracked struct FlatSubtreeMut<'a, C: PageTableConfig> {
    pub nodes: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub remainder: &'a mut Map<Paddr, FlatNodeRecord<C>>,
    pub permissions: &'a mut Map<Paddr, FracMetadataPerm>,
    pub permission_remainder: &'a mut Map<Paddr, FracMetadataPerm>,
    pub ghost root: Paddr,
}

impl<'a, C: PageTableConfig> FlatSubtreeMut<'a, C> {
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
