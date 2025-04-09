use vstd::prelude::*;

use crate::mm::{
    meta::AnyFrameMeta, nr_subpage_per_huge, page_prop::PageProperty, page_size,
    page_table::zeroed_pt_pool, vm_space::Token, PageTableEntryTrait, PagingConstsTrait,
};

use super::{Child, MapTrackingStatus, PageTableLockTrait, PageTableNode};

use crate::exec;

verus! {
/// A view of an entry in a page table node.
///
/// It can be borrowed from a node using the [`PageTableLock::entry`] method.
///
/// This is a static reference to an entry in a node that does not account for
/// a dynamic reference count to the child. It can be used to create a owned
/// handle, which is a [`Child`].
pub struct Entry<'a, E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    // node: &'a mut PageTableLock<E, C>,
    pub node: &'a PTL,
    pub phantom: std::marker::PhantomData<(E, C)>,
}

impl<'a, E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>> Entry<'a, E, C, PTL> {


    /// Gets a reference to the child.
    pub(in crate::mm) fn to_ref<T: AnyFrameMeta>(&self, mpt: &exec::MockPageTable) -> (res: Child<E, C, T>)
    requires
        mpt.wf(),
        self.pte.pte_paddr() == exec::get_pte_from_addr_spec(self.pte.pte_paddr(), mpt).pte_addr,
        self.pte.frame_paddr() == exec::get_pte_from_addr_spec(self.pte.pte_paddr(), mpt).frame_pa,
    ensures
        if (mpt.ptes@.value().contains_key(self.pte.pte_paddr() as int)) {
            match res {
                Child::PageTableRef(pt) =>
                    pt == self.pte.frame_paddr() as usize && mpt.frames@.value().contains_key(pt as int),
                _ => false,
            }
        } else {
            match res {
                Child::None => true,
                _ => false,
            }
        },
    {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        // unsafe { Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), false) }
        let c = Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), false,
                                                    mpt);
        c
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    // TODO: Implement protect
    #[verifier::external_body]
    pub(in crate::mm) fn protect(
        &mut self,
        prot_op: &mut impl FnMut(&mut PageProperty),
        token_op: &mut impl FnMut(&mut Token),
    ) {
        // if self.pte.is_present() {
        //     // Protect a proper mapping.
        //     let prop = self.pte.prop();
        //     let mut new_prop = prop;
        //     prot_op(&mut new_prop);

        //     if prop == new_prop {
        //         return;
        //     }

        //     self.pte.set_prop(new_prop);
        // } else {
        //     let paddr = self.pte.paddr();
        //     if paddr == 0 {
        //         // Not mapped.
        //         return;
        //     } else {
        //         // Protect a token.

        //         // SAFETY: The physical address was written as a valid token.
        //         let mut token = unsafe { Token::from_raw_inner(paddr) };
        //         token_op(&mut token);
        //         self.pte.set_paddr(token.into_raw_inner());
        //     }
        // }

        // // SAFETY:
        // //  1. The index is within the bounds.
        // //  2. We replace the PTE with a new one, which differs only in
        // //     `PageProperty`, so it is still compatible with the current
        // //     page table node.
        // unsafe { self.node.write_pte(self.idx, self.pte) };
        unimplemented!()
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Panics
    ///
    /// The method panics if the given child is not compatible with the node.
    /// The compatibility is specified by the [`Child::is_compatible`].
    // TODO: Implement replace
    // #[verifier::external_body]
    pub(in crate::mm) fn replace<T: AnyFrameMeta>(self, new_child: Child<E, C, T>) -> (res: Child<E, C, T>)
    {
        // // assert!(new_child.is_compatible(self.node.level(), self.node.is_tracked()));

        // SAFETY: The entry structure represents an existent entry with the
        // right node information. The old PTE is overwritten by the new child
        // so that it is not used anymore.
        let old_child =
            // unsafe { Child::from_pte(self.pte, self.node.level(), self.node.is_tracked()) };
            unsafe { Child::from_pte(self.pte, self.node.level(), self.node.is_tracked()) };

        if old_child.is_none() && !new_child.is_none() {
            // *self.node.nr_children_mut() += 1;
            self.node.change_children(1);
        } else if !old_child.is_none() && new_child.is_none() {
            // *self.node.nr_children_mut() -= 1;
            self.node.change_children(-1);
        }

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is compatible with the page table node, as asserted above.
        // unsafe { self.node.write_pte(self.idx, new_child.into_pte()) };
        self.node.write_pte(self.idx, new_child.into_pte());

        old_child
        // unimplemented!()
    }

    /// Create a new entry at the node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    // pub(super) unsafe fn new_at(node: &'a mut PageTableLock<E, C>, idx: usize) -> Self {
    pub fn new_at(node: &'a PTL, idx: usize, mpt: &exec::MockPageTable) -> (res: Self)
    requires
        idx < nr_subpage_per_huge(),
    ensures
        res.pte.pte_paddr() == node.paddr() as usize + idx * exec::SIZEOF_PAGETABLEENTRY,
        res.pte.pte_paddr() == exec::get_pte_from_addr_spec(res.pte.pte_paddr(), mpt).pte_addr,
        res.pte.frame_paddr() == exec::get_pte_from_addr_spec(res.pte.pte_paddr(), mpt).frame_pa,
    {
        // SAFETY: The index is within the bound.
        // let pte = unsafe { node.read_pte(idx) };
        let pte = node.read_pte(idx, mpt);
        assert (pte.frame_paddr() < usize::MAX) by { admit(); }; // TODO
        Self { pte, idx, node, phantom: std::marker::PhantomData }
    }
}

}
