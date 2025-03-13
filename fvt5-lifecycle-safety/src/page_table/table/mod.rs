pub mod model;
pub mod specs;

use vstd::prelude::*;
use aster_common::prelude::*;

// --- Model ---

verus! {

    pub tracked struct ConcretePageTableModel (
        pub tracked PageTableTreeModel,
    );

    pub tracked struct IntermediatePageTableModel (
        pub tracked PageTablePathModel,
    );

    pub tracked struct FlatPageTableModel (
        pub tracked PageTableMapModel,
    );

}

verus! {

impl ConcretePageTableModel {

    pub open spec fn inv(self) -> bool {
        self.0.inv()
    }

    #[verifier::returns(proof)]
    pub proof fn borrow_tree(#[verifier::proof] &self) -> Tracked<&PageTableTreeModel>
    {
        Tracked(&self.0)
    }

    #[verifier::inline]
    pub open spec fn on_tree(self, node: PageTableNodeModel) -> bool
        recommends
            self.inv(),
            node@.inv(),
    {
        self.0@.on_tree(node@)
    }

    pub open spec fn get_node(self, path: PageTableTreePathModel) -> Option<PageTableNodeModel>
        recommends
            self.inv(),
            path.inv(),
    {
        let res = self.0@.visit(path@);
        if res.len() == path@.len() {
            Some(PageTableNodeModel::from_node(res.last()))
        } else {
            None
        }
    }

    pub open spec fn get_path(self, node: PageTableNodeModel) ->
        (res: PageTableTreePathModel)
        recommends
            self.inv(),
            node@.inv(),
            self.0@.on_tree(node@),
    {
        PageTableTreePathModel::from_path(
            self.0@.get_path(node@)
        )
    }

}

}
