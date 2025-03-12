use vstd::prelude::*;

use crate::PageTableEntryTrait;
use crate::PageTableEntry;
use crate::PagingConstsTrait;
use crate::PagingConsts;

use super::PageTableNode;

// use crate::prelude::{RawPageTableNode, PageProperty, Paddr, PagingLevel, DynPage};

verus! {

/// A child of a page table node.
///
/// This is a owning handle to a child of a page table node. If the child is
/// either a page table node or a page, it holds a reference count to the
/// corresponding page.
// #[derive(Debug)] // TODO: Debug for Child
pub(in crate::mm) enum Child<
    // E: PageTableEntryTrait = PageTableEntry,
    // C: PagingConstsTrait = PagingConsts,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
> where
    // [(); C::NR_LEVELS as usize]:,
{
    // /// A owning handle to a raw page table node.
    PageTable(PageTableNode<E, C>),
    // /// A reference of a child page table node, in the form of a physical
    // /// address.
    // TODO: PageTableRef
    // PageTableRef(ManuallyDrop<PageTableNode<E, C>>),
    // /// A mapped frame.
    // TODO: Frame(Frame<dyn AnyFrameMeta>),
    // Frame(Frame<dyn AnyFrameMeta>, PageProperty),
    // /// Mapped frames that are not tracked by handles.
    // TODO: Untracked
    // Untracked(Paddr, PagingLevel, PageProperty),
    // TODO: Token
    // Token(Token),
    None,
}

// impl Child {
impl<E: PageTableEntryTrait, C: PagingConstsTrait> Child<E, C> {

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

}
