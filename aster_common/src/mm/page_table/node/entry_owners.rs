use vstd::prelude::*;

use vstd::simple_pptr::PointsTo;
use vstd_extra::array_ptr;

use super::*;

verus! {

pub tracked struct NodeEntryOwner<'rcu, C: PageTableConfig> {
    pub as_node: NodeOwner<C>,
    pub guard_perm: Tracked<PointsTo<PageTableGuard<'rcu, C>>>,
    // TODO: this corresponds to the `node` pointers of the children, NOT of this node's entry!
    pub children_perm: array_ptr::PointsTo<Entry<'rcu, C>, CONST_NR_ENTRIES>,
    pub slot_perm: Tracked<PointsTo<MetaSlot>>,
}

impl<'rcu, C: PageTableConfig> Inv for NodeEntryOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.guard_perm@.is_init()
        &&& self.guard_perm@.value().inner.inner.ptr == self.slot_perm@.pptr()
        &&& self.guard_perm@.value().inner.inner.wf(self.as_node)
        &&& self.as_node.inv()
        &&& self.slot_perm@.is_init()
        &&& self.slot_perm@.value().storage == self.as_node.meta_perm@.points_to@.pptr()
        &&& self.as_node.meta_perm@.pptr().ptr.0 == self.slot_perm@.value().storage.addr()
        &&& self.as_node.meta_perm@.pptr().addr == self.slot_perm@.value().storage.addr()
        &&& meta_to_frame(self.slot_perm@.addr()) < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()
        &&& forall |i:int|
            0 <= i < NR_ENTRIES() ==>
            self.children_perm.is_init(i as int) ==>
            {
                &&& self.children_perm.opt_value()[i as int].value().node == self.guard_perm@.pptr()
            }
    }
}

impl<'rcu, C: PageTableConfig> NodeEntryOwner<'rcu, C> {
    pub open spec fn relate_slot_owner(self, slot_own: &MetaSlotOwner) -> bool {
        &&& slot_own.inv()
        &&& self.slot_perm@.value().wf(*slot_own)
        &&& self.slot_perm@.addr() == slot_own.self_addr
    }
}

// Verus support for enums is... iffy. So we simulate it with a struct.
pub tracked struct ChildOwner<'rcu, C: PageTableConfig> {
    pub node: Option<NodeEntryOwner<'rcu, C>>,
    pub frame: Option<(usize, PageProperty)>,
    pub locked: Option<Ghost<EntryView<C>>>
}

impl<'rcu, C: PageTableConfig> Inv for ChildOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.node is Some ==> {
            &&& self.frame is None
            &&& self.locked is None
            &&& self.node.unwrap().inv()
        }
        &&& self.frame is Some ==> self.node is None && self.locked is None
        &&& self.locked is Some ==> self.frame is None && self.node is None
    }
}

impl<'rcu, C: PageTableConfig> ChildOwner<'rcu, C> {
    pub open spec fn is_node(self) -> bool {
        self.node is Some
    }

    pub open spec fn is_frame(self) -> bool {
        self.frame is Some
    }
    
    pub open spec fn is_locked(self) -> bool {
        self.locked is Some
    }

    pub open spec fn is_absent(self) -> bool {
        self.node is None && self.frame is None && self.locked is None
    }
}

pub tracked struct EntryOwner<'rcu, C: PageTableConfig> {
    pub as_child: ChildOwner<'rcu, C>,
    pub base_addr: usize,
    pub index: usize,
    pub path: Ghost<Seq<IntermediatePageTableEntryView<C>>>,
}

impl<'rcu, C: PageTableConfig> Inv for EntryOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.as_child.inv()
    }
}

impl <'rcu, C: PageTableConfig> View for EntryOwner<'rcu, C> {
    type V = EntryView<C>;

    #[verifier::external_body]
    open spec fn view(&self) -> <Self as View>::V {
        if let Some((paddr, prop)) = self.as_child.frame {
            EntryView::Leaf(LeafPageTableEntryView{
                map_va: 0, // TODO: compute from the path the virtual address the entry maps
                frame_pa: self.base_addr as int, // TODO: track or compute the phys address of the node the entry is part of
                in_frame_index: self.index as int, // TODO: track or compute the entry's index within its node
                map_to_pa: paddr as int,
                level: (self.path@.len() + 1) as u8,
                prop: prop,
                phantom: PhantomData
            })
        }
        else if let Some(node) = self.as_child.node {
            EntryView::Intermediate(IntermediatePageTableEntryView{
                map_va: 0, // TODO: as above
                frame_pa: self.base_addr as int,
                in_frame_index: self.index as int,
                map_to_pa: meta_to_frame(node.slot_perm@.addr()) as int,
                level: (self.path@.len() + 1) as u8,
                phantom: PhantomData
           })
        } else if let Some(view) = self.as_child.locked {
            view@
        } else {
            EntryView::Absent
        }
    }
}

impl<'rcu, C: PageTableConfig> InvView for EntryOwner<'rcu, C> {
    proof fn view_preserves_inv(self) { }
}

impl<'rcu, C: PageTableConfig> OwnerOf for Entry<'rcu, C> {
    type Owner = EntryOwner<'rcu, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.idx < NR_ENTRIES()
        &&& self.pte.paddr() % PAGE_SIZE() == 0
        &&& self.pte.paddr() < MAX_PADDR()
    }
}

} // verus!
