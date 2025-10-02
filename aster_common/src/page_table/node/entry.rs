use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::cell;

use crate::prelude::{
    FrameRef, PageTableConfig, PageTableEntry, PageTableEntryTrait, PageTablePageMeta, PageTableNode, MetaSlot, MetaSlotOwner
};

use vstd_extra::ownership::*;

use std::ops::Deref;
use std::marker::PhantomData;

verus! {

/// A reference to a page table node.
pub type PageTableNodeRef<'a, C: PageTableConfig> = FrameRef<'a, PageTablePageMeta<C>>;

/// A guard that holds the lock of a page table node.
#[rustc_has_incoherent_inherent_impls]
pub struct PageTableGuard<'rcu, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Deref for PageTableGuard<'rcu, C> {
    type Target = PageTableNodeRef<'rcu, C>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[rustc_has_incoherent_inherent_impls]
pub struct Entry<'slot, 'rcu, C: PageTableConfig> {
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
    pub node: PPtr<PageTableGuard<'rcu, C>>,

    /// For proof purposes, we need to track the lifetime of the metaslot that holds this entry,
    /// so we put it in a PhantomData field
    pub slot: PhantomData<&'slot MetaSlot>,
}

impl<'slot, 'rcu, C: PageTableConfig> Entry<'slot, 'rcu, C> {
    pub open spec fn new_spec(pte: C::E, idx: usize, node: PPtr<PageTableGuard<'rcu, C>>) -> Self {
        let slot = PhantomData;
        Self { pte, idx, node, slot }
    }

    #[verifier::when_used_as_spec(new_spec)]
    pub fn new(pte: C::E, idx: usize, node: PPtr<PageTableGuard<'rcu, C>>) -> Self {
        let slot = PhantomData;
        Self { pte, idx, node, slot }
    }
}

} // verus!
