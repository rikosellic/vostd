use vstd::prelude::*;

use vstd_extra::ownership::*;

use std::marker::PhantomData;

use super::*;

verus! {

pub ghost struct FrameView<C: PageTableConfig> {
    pub map_va: int,
    pub pa: int,
    /// A map from the ancestor frame level to the PTE that the ancestor maps to its child.
    pub ancestor_chain: Map<int, IntermediatePageTableEntryView<C>>,
    pub level: PagingLevel,
    pub phantom: PhantomData<C>,
}

impl<C: PageTableConfig> Inv for FrameView<C> {
    open spec fn inv(self) -> bool {
        true/*
        &&& pa_is_valid_pt_address(self.pa)
        &&& level_is_in_range::<C>(self.level as int)
        // The corresponding virtual address must be aligned to the upper-level page size.
        &&& self.map_va % (page_size_spec::<C>((self.level + 1) as PagingLevel) as int) == 0
        // Ancestor properties.
        &&& forall|ancestor_level: int| #[trigger]
            self.ancestor_chain.contains_key(ancestor_level) ==> {
                &&& level_is_in_range::<C>(ancestor_level)
                &&& self.level < ancestor_level
                &&& self.ancestor_chain[ancestor_level].wf()
                &&& self.ancestor_chain[ancestor_level].level
                    == ancestor_level
                // No loops.
                &&& #[trigger] self.ancestor_chain[ancestor_level].frame_pa
                    != self.pa
                // The map-to-addresses actually forms a chain.
                &&& if ancestor_level == self.level + 1 {
                    self.ancestor_chain[ancestor_level].map_to_pa == self.pa
                } else {
                    &&& self.ancestor_chain.contains_key(ancestor_level - 1)
                        ==> #[trigger] self.ancestor_chain[ancestor_level].map_to_pa
                        == self.ancestor_chain[ancestor_level - 1].frame_pa
                }
                &&& if self.ancestor_chain.contains_key(ancestor_level + 1) {
                    self.ancestor_chain[ancestor_level + 1].map_to_pa
                        == self.ancestor_chain[ancestor_level].frame_pa
                } else {
                    true
                }
                // The ancestor is not duplicate.
                &&& forall|other_ancestor_level: int| #[trigger]
                    self.ancestor_chain.contains_key(other_ancestor_level) ==> {
                        ||| other_ancestor_level == ancestor_level
                        ||| self.ancestor_chain[other_ancestor_level]
                            != self.ancestor_chain[ancestor_level]
                    }
            }
        */

    }
}

pub tracked struct Mapping {
    pub tracked pa: usize,
    pub tracked is_locked: bool,
    pub page_size:
        usize,/*  TODO: below are some "payload" fields that do not directly impact verification of the page table,
            but which will be important for the long-term goal of merging verification targets into a single,
            end-to-end verified system. We omit these for now.
        pub flags: PageFlags,
        pub privilege: PrivilegedPageFlags,
        pub cache: CachePolicy, */
}

impl Mapping {
    pub open spec fn inv(self) -> bool {
        &&& set![4096, 2097152, 1073741824].contains(self.page_size)
        &&& self.pa % self.page_size == 0
    }
}

pub type PageTableFlatView = Map<usize, Option<Mapping>>;

} // verus!
