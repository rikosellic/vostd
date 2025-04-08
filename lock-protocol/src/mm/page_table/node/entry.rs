use vstd::prelude::*;

use crate::mm::{
    meta::AnyFrameMeta, nr_subpage_per_huge, page_prop::PageProperty, page_size,
    page_table::zeroed_pt_pool, vm_space::Token, PageTableEntryTrait, PagingConstsTrait,
};

use super::{Child, MapTrackingStatus, PageTableLockTrait, PageTableNode};

use crate::exec::SIZEOF_PAGETABLEENTRY;

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
    /// Returns if the entry does not map to anything.
    pub(in crate::mm) fn is_none(&self) -> bool {
        !self.pte.is_present() && self.pte.paddr() == 0
    }

    /// Returns if the entry is marked with a token.
    pub(in crate::mm) fn is_token(&self) -> bool {
        !self.pte.is_present() && self.pte.paddr() != 0
    }

    /// Returns if the entry maps to a page table node.
    pub(in crate::mm) fn is_node(&self) -> bool {
        self.pte.is_present() && !self.pte.is_last(self.node.level())
    }

    /// Gets a owned handle to the child.
    pub(in crate::mm) fn to_owned<T: AnyFrameMeta>(&self) -> Child<E, C, T> {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        unsafe { Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), true) }
    }

    /// Gets a reference to the child.
    pub(in crate::mm) fn to_ref<T: AnyFrameMeta>(&self) -> (res: Child<E, C, T>)
    ensures
        match res {
            Child::None => true,
            Child::PageTableRef(_) => true,
            _ => false,
        }
    {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        // unsafe { Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), false) }
        let c = Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), false);
        assert(match c {
            Child::None => true,
            Child::PageTableRef(_) => true,
            _ => false,
        }) by { admit(); }; // TODO
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

    /// Splits the entry to smaller pages if it maps to a untracked huge page.
    ///
    /// If the entry does map to a untracked huge page, it is split into smaller
    /// pages mapped by a child page table node. The new child page table node
    /// is returned.
    ///
    /// If the entry does not map to a untracked huge page, the method returns
    /// `None`.
    // TODO: Implement split_if_untracked_huge
    #[verifier::external_body]
    pub(in crate::mm) fn split_if_untracked_huge(self) -> Option<PTL> {
        let level = self.node.level();

        if !(self.pte.is_last(level)
            && level > 1
            && self.node.is_tracked() == MapTrackingStatus::Untracked)
        {
            return None;
        }

        let pa = self.pte.paddr();
        let prop = self.pte.prop();

        let preempt_guard = crate::task::disable_preempt();
        let mut new_page =
            zeroed_pt_pool::alloc::<E, C, PTL>(&preempt_guard, level - 1, MapTrackingStatus::Untracked);
        for i in 0..nr_subpage_per_huge() {
            let small_pa = pa + i * page_size::<C>(level - 1);
            // let _ = new_page
            //     .entry(i)
            //     .replace(Child::<E, C, ()>::Untracked(small_pa, level - 1, prop));
            Entry::new_at(&new_page, i)
                    .replace(Child::<E, C, ()>::Untracked(small_pa, level - 1, prop));
        }
        let pt_paddr = new_page.into_raw_paddr();
        // SAFETY: It was forgotten at the above line.
        let _ = self.replace(Child::<E, C, ()>::PageTable(unsafe {
            PageTableNode::from_raw(pt_paddr)
        }));
        // SAFETY: `pt_paddr` points to a PT that is attached to the node,
        // so that it is locked and alive.
        Some(unsafe { PTL::from_raw_paddr(pt_paddr) })
    }

    /// Splits the entry into a child that is marked with a same token.
    ///
    /// This method returns [`None`] if the entry is not marked with a token or
    /// it is in the last level.
    // TODO: Implement split_if_untracked_huge
    #[verifier::external_body]
    pub(in crate::mm) fn split_if_huge_token(self) -> Option<PTL> {
        let level = self.node.level();

        if !(!self.pte.is_present() && level > 1 && self.pte.paddr() != 0) {
            return None;
        }

        // SAFETY: The physical address was written as a valid token.
        let token = unsafe { Token::from_raw_inner(self.pte.paddr()) };

        let preempt_guard = crate::task::disable_preempt();
        let mut new_page =
            zeroed_pt_pool::alloc::<E, C, PTL>(&preempt_guard, level - 1, self.node.is_tracked());
        for i in 0..nr_subpage_per_huge() {
            // let _ = new_page.entry(i).replace(Child::<E, C, ()>::Token(token));
            Entry::new_at(&new_page, i).replace(Child::<E, C, ()>::Token(token.clone()));
        }
        let pt_paddr = new_page.into_raw_paddr();
        let _ = self.replace(Child::<E, C, ()>::PageTable(unsafe {
            PageTableNode::from_raw(pt_paddr)
        }));

        Some(unsafe { PTL::from_raw_paddr(pt_paddr) })
    }

    /// Create a new entry at the node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    // pub(super) unsafe fn new_at(node: &'a mut PageTableLock<E, C>, idx: usize) -> Self {
    pub fn new_at(node: &'a PTL, idx: usize) -> (res: Self)
    requires
        idx < nr_subpage_per_huge(),
    ensures
        res.pte.paddr() < usize::MAX,
    {
        // SAFETY: The index is within the bound.
        // let pte = unsafe { node.read_pte(idx) };
        let pte = node.read_pte(idx);
        assert (pte.paddr() < usize::MAX) by { admit(); }; // TODO
        Self { pte, idx, node, phantom: std::marker::PhantomData }
    }
}

}
