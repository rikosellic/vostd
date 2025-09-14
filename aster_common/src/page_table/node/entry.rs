use vstd::prelude::*;
use vstd::simple_pptr;
use vstd::cell;

use crate::prelude::{
    FrameRef, PageTableConfig, PageTableEntry, PageTableEntryTrait, PageTablePageMeta, PageTableNode, MetaSlot, MetaSlotOwner
};

use vstd_extra::ownership::*;

verus! {

/// A reference to a page table node.
pub type PageTableNodeRef<'a, C: PageTableConfig> = FrameRef<'a, PageTablePageMeta<C>>;

/// A guard that holds the lock of a page table node.
#[rustc_has_incoherent_inherent_impls]
pub struct PageTableGuard<'rcu, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'rcu, C>,
}

#[rustc_has_incoherent_inherent_impls]
pub struct Entry<'a, 'rcu, C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: &'a /*mut*/ PageTableGuard<'rcu, C>,
}

impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    pub open spec fn new_spec(pte: C::E, idx: usize, node: &'a PageTableGuard<'rcu, C>) -> Self {
        Self { pte, idx, node }
    }

    #[verifier::when_used_as_spec(new_spec)]
    pub fn new(pte: C::E, idx: usize, node: &'a PageTableGuard<'rcu, C>) -> Self {
        Self { pte, idx, node }
    }

/*    pub fn is_node(
        &self,
        Tracked(p_slot): Tracked<&simple_pptr::PointsTo<MetaSlot>>,
        owner: MetaSlotOwner,
    ) -> bool
        requires
            self.node.inv(),
            p_slot.pptr() == self.node.ptr,
            p_slot.is_init(),
            p_slot.value().wf(&owner),
            is_variant(owner.view().storage.value(), "PTNode"),
    {
        self.pte.is_present() && !self.pte.is_last(
            self.node.level(Tracked(p_slot), owner),
        )
    }*/
}

} // verus!
