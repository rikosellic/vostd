use vstd::prelude::*;

use crate::prelude::{PageTableConfig, PageTableNode, RawPageTableNode, PageProperty, Paddr, PagingLevel, DynPage};

verus! {

/// A page table entry that owns the child of a page table node if present.
#[rustc_has_incoherent_inherent_impls]
pub enum Child<C: PageTableConfig> {
    /// A child page table node.
    pub PageTable(/*RcuDrop<*/PageTableNode<C>/*>*/),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    pub Frame(Paddr, PagingLevel, PageProperty),
    pub None,
}

impl<C: PageTableConfig> Child<C> {
    #[verifier::inline]
    pub open spec fn is_none_spec(&self) -> bool {
        match self {
            Child::None => true,
            _ => false,
        }
    }

    #[verifier::when_used_as_spec(is_none_spec)]
    pub fn is_none(&self) -> bool {
        match self {
            Child::None => true,
            _ => false,
        }
    }
}

} // verus!
