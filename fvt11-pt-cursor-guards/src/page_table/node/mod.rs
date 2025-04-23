pub mod model;

use aster_common::x86_64::PagingConsts;
use model::{pt_node_write_pte, pt_node_free};
use vstd::prelude::*;
use vstd_extra::array_ptr::*;
use vstd::raw_ptr;
use vstd::simple_pptr::*;

use aster_common::prelude::*;
use aster_common::page_table::node::*;
use aster_common::x86_64::page_table_entry::*;
use aster_common::x86_64::kspace::*;
use aster_common::x86_64::mm::*;
use aster_common::page::meta::*;
use aster_common::page::Page;

use crate::page_table::node::model::{NR_ENTRIES, NR_LEVELS};
use core::marker::PhantomData;
use std::borrow::BorrowMut;

verus! {

impl RawPageTableNode {
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, model: PageTableNodeValue) -> bool {
        self.paddr() == model.paddr()
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn clone_shallow(&self, Tracked(model): Tracked<&mut PageTableNodeModel>) -> (res:
        RawPageTableNode)
        requires
            self.inv(),
            self.relate((*old(model))@.value),
        ensures
            res.inv(),
            res.relate((*model)@.value),
    {
        unimplemented!()/*        model.borrow_mut().value.nr_raws = model.borrow().value.nr_raws + 1;
        Self {
            raw: self.raw,
            level: self.level,
            _phantom: PhantomData,
        } */

    }

    /// Converts a raw handle to an accessible handle by pertaining the lock.
    #[rustc_allow_incoherent_impl]
    pub(super) fn lock(self) -> PageTableNode {
        PageTableNode { page: Page { ptr: PPtr::from_addr(self.paddr()), _marker: PhantomData } }
    }
}

impl PageTableNode {
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, model: PageTableNodeValue) -> bool {
        &&& self.paddr() == model.paddr()
        &&& model.is_locked == true
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn relate_implies_inv(self, model: PageTableNodeModel)
        requires
            self.inv(),
            self.relate(model@.value),
        ensures
            model@.inv(),
    {
        admit();
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn read_pte(&self, idx: usize, model: Tracked<&PageTableNodeModel>) -> (res: PageTableEntry)
        requires
            self.inv(),
            self.relate((*model@)@.value),
            idx < NR_ENTRIES,
            model@@.value.perms.unwrap().opt_value()[idx as int].is_init(),
        ensures
            model@@.value.perms.unwrap().opt_value()[idx as int].value() == res,
    {
        proof {
            self.relate_implies_inv(*model@);
            lemma_meta_frame_vaddr_properties(self.page.ptr.addr());
            lemma_max_paddr_range();
        }
        let ptr = ArrayPtr::<PageTableEntry, NR_ENTRIES>::from_addr(paddr_to_vaddr(self.paddr()));
        let tracked perms = model.borrow()@.borrow_value().borrow_perms().tracked_borrow();
        ptr.get(Tracked(&perms), idx)
    }

    #[rustc_allow_incoherent_impl]
    pub fn write_pte(
        &self,
        idx: usize,
        entry: PageTableEntry,
        Tracked(model): Tracked<&mut PageTableNodeModel>,
    )
        requires
            self.inv(),
            self.relate((*old(model))@.value),
            idx < NR_ENTRIES,
        ensures
            model@.value.perms.unwrap().opt_value()[idx as int].value() == entry,
    {
        proof {
            self.relate_implies_inv(*model);
            lemma_meta_frame_vaddr_properties(self.page.ptr.addr());
            lemma_max_paddr_range();
        }
        let ptr = ArrayPtr::<PageTableEntry, NR_ENTRIES>::from_addr(paddr_to_vaddr(self.paddr()));
        pt_node_write_pte(Tracked(model), ptr, idx, entry);
    }

    #[rustc_allow_incoherent_impl]
    pub fn drop(&self, Tracked(model): Tracked<PageTableNodeModel>)
        requires
            self.inv(),
            model@.inv(),
            self.relate(model@.value),
            model@.value.perms.unwrap().is_uninit_all(),
    {
        let ptr = ArrayPtr::<PageTableEntry, NR_ENTRIES>::from_addr(paddr_to_vaddr(self.paddr()));
        pt_node_free(Tracked(model), ptr);
    }
}

} // verus!
