use std::clone;
use std::mem::ManuallyDrop;

use vstd::prelude::*;

use crate::mm::meta::AnyFrameMeta;
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::Token;
use crate::mm::Frame;
use crate::mm::Paddr;
use crate::mm::PageTableEntryTrait;
use crate::mm::PagingConstsTrait;
use crate::mm::PagingConsts;
use crate::mm::PagingLevel;

use super::MapTrackingStatus;
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
    T: AnyFrameMeta
> {
    /// A owning handle to a raw page table node.
    PageTable(PageTableNode<E, C>),
    /// A reference of a child page table node, in the form of a physical
    /// address.
    PageTableRef(Paddr),
    /// A mapped frame.
    Frame(Frame<T>, PageProperty),
    /// Mapped frames that are not tracked by handles.
    Untracked(Paddr, PagingLevel, PageProperty),
    Token(Token),
    None,
}

// impl Child {
impl<E: PageTableEntryTrait, C: PagingConstsTrait, T: AnyFrameMeta> Child<E, C, T> {

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

    /// Returns whether the child is compatible with the given node.
    ///
    /// In other words, it checks whether the child can be a child of a node
    /// with the given level and tracking status.
    // TODO: Implement is_compatible
    #[verifier::external_body]
    pub(super) fn is_compatible(
        &self,
        node_level: PagingLevel,
        is_tracked: MapTrackingStatus,
    ) -> bool {
        match self {
            Child::PageTable(pt) => node_level == pt.level() + 1,
            Child::PageTableRef(_) => false,
            Child::Frame(p, _) => {
                node_level == p.map_level()
                // && is_tracked == MapTrackingStatus::Tracked
            }
            Child::Untracked(_, level, _) => {
                node_level == *level
                // && is_tracked == MapTrackingStatus::Untracked
            }
            Child::None | Child::Token(_) => true,
        }
    }

    /// Converts a child into a owning PTE.
    ///
    /// By conversion it loses information about whether the page is tracked
    /// or not. Also it loses the level information. However, the returned PTE
    /// takes the ownership (reference count) of the child.
    ///
    /// Usually this is for recording the PTE into a page table node. When the
    /// child is needed again by reading the PTE of a page table node, extra
    /// information should be provided using the [`Child::from_pte`] method.
    pub(super) fn into_pte(self) -> E {
        match self {
            Child::PageTable(pt) => {
                // let pt = ManuallyDrop::new(pt);
                E::new_pt(pt.start_paddr())
            }
            Child::PageTableRef(_) => {
                // panic!("`PageTableRef` should not be converted to PTE");
                // TODO
                E::new_absent()
            }
            Child::Frame(page, prop) => {
                let level = page.map_level();
                E::new_page(page.into_raw(), level, prop)
            }
            Child::Untracked(pa, level, prop) => E::new_page(pa, level, prop),
            Child::None => E::new_absent(),
            Child::Token(token) => E::new_token(token),
        }
    }

    /// Converts a PTE back to a child.
    ///
    /// # Safety
    ///
    /// The provided PTE must be originated from [`Child::into_pte`]. And the
    /// provided information (level and tracking status) must be the same with
    /// the lost information during the conversion. Strictly speaking, the
    /// provided arguments must be compatible with the original child (
    /// specified by [`Child::is_compatible`]).
    ///
    /// This method should be only used no more than once for a PTE that has
    /// been converted from a child using the [`Child::into_pte`] method.
    // TODO: Implement the conversion from PTE.
    #[verifier::external_body]
    pub(super) unsafe fn from_pte(
        pte: E,
        level: PagingLevel,
        is_tracked: MapTrackingStatus,
    ) -> Self {
        unimplemented!()
    }

    /// Gains an extra reference to the child.
    ///
    /// If the child is a frame, it increases the reference count of the frame.
    ///
    /// If the child is a page table node, the returned value depends on
    /// `clone_raw`:
    ///  - If `clone_raw` is `true`, it returns a new owning handle to the page
    ///    table node ([`Child::PageTable`]).
    ///  - If `clone_raw` is `false`, it returns a reference to the page table
    ///    node ([`Child::PageTableRef`]).
    ///
    /// # Safety
    ///
    /// The provided PTE must be originated from [`Child::into_pte`], which is
    /// the same requirement as the [`Child::from_pte`] method.
    ///
    /// This method must not be used with a PTE that has been restored to a
    /// child using the [`Child::from_pte`] method.
    // TODO: Implement the conversion from PTE.
    // #[verifier::external_body]
    pub(super) fn ref_from_pte(
        pte: &E,
        level: PagingLevel,
        is_tracked: MapTrackingStatus,
        clone_raw: bool,
    ) -> (res: Self)
    ensures
        if (clone_raw) {
            match res {
                Child::None => true,
                Child::PageTable(_) => true,
                _ => false,
            }
        } else {
            match res {
                Child::None => true,
                Child::PageTableRef(_) => true,
                _ => false,
            }
        }
    {
        if !pte.is_present() {
            // let paddr = pte.paddr();
            // if paddr == 0 {
            //     return Child::None;
            // } else {
            //     // SAFETY: The physical address is written as a valid token.
            //     return Child::Token(unsafe { Token::from_raw_inner(paddr) });
            // }

            // TODO: We currently do not model Child::Token

            return Child::None;
        }

        let paddr = pte.frame_paddr();

        // TODO: Model is_last
        // if !pte.is_last(level) {
            if clone_raw {
                // SAFETY: The physical address is valid and the PTE already owns
                // the reference to the page.
                // unsafe { inc_frame_ref_count(paddr) }; // TODO
                // SAFETY: The physical address points to a valid page table node
                // at the given level.
                // let pt = unsafe { PageTableNode::from_raw(paddr) };
                let pt = PageTableNode::from_raw(paddr);
                assert(pt.ptr == paddr);
                assert(paddr == pte.frame_paddr());
                assert(pt.ptr == pte.frame_paddr());
                // debug_assert_eq!(pt.level(), level - 1);
                return Child::PageTable(pt);
            } else {
                return Child::PageTableRef(paddr);
            }
        // }

        // TODO: model is_tracked
        // match is_tracked {
        //     MapTrackingStatus::Tracked => {
        //         // SAFETY: The physical address is valid and the PTE already owns
        //         // the reference to the page.
        //         // unsafe { inc_frame_ref_count(paddr) }; // TODO
        //         // SAFETY: The physical address points to a valid page.
        //         let page = unsafe { Frame::<T>::from_raw(paddr) };
        //         Child::Frame(page, pte.prop())
        //     }
        //     MapTrackingStatus::Untracked => Child::Untracked(paddr, level, pte.prop()),
        //     MapTrackingStatus::NotApplicable =>
        //         // panic!("Invalid tracking status"),
        //         Child::None, // TODO

        // }
    }

}

}
