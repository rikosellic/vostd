use vstd::prelude::*;

use super::*;

verus! {

/// A page table entry that owns the child of a page table node if present.
#[rustc_has_incoherent_inherent_impls]
pub enum Child<C: PageTableConfig> {
    /// A child page table node.
    pub PageTable(  /*RcuDrop<*/ PageTableNode<C>  /*>*/ ),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    pub Frame(Paddr, PagingLevel, PageProperty),
    pub None,
}

impl<C: PageTableConfig> Child<C> {
    pub open spec fn get_node(self) -> Option<PageTableNode<C>> {
        match self {
            Self::PageTable(node) => Some(node),
            _ => None,
        }
    }

    pub open spec fn get_frame_tuple(self) -> Option<(Paddr, PagingLevel, PageProperty)> {
        match self {
            Self::Frame(paddr, level, prop) => Some((paddr, level, prop)),
            _ => None,
        }
    }

    #[verifier::inline]
    pub open spec fn is_none_spec(&self) -> bool {
        match self {
            Child::None => true,
            _ => false,
        }
    }

    /// Returns whether the child is not present.
    #[verifier::when_used_as_spec(is_none_spec)]
    pub fn is_none(&self) -> (b: bool)
        ensures
            b == self.is_none_spec(),
    {
        matches!(self, Child::None)
    }
}

/// A reference to the child of a page table node.
#[rustc_has_incoherent_inherent_impls]
pub enum ChildRef<'a, C: PageTableConfig> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a, C>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

} // verus!
