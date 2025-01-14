use vstd::prelude::*;

use vstd_extra::prelude::{TreePath};
use aster_common::prelude::*;

verus! {

pub tracked struct ConcreteCursor {
    pub tracked tree: PageTableTreeModel,
    pub tracked locked_subtree: PageTableNodeModel,
    pub tracked path: PageTableTreePathModel,
}

impl ConcreteCursor {

    pub open spec fn inv(self) -> bool {
    &&& self.tree.inv()
    &&& self.path.inv()
    &&& self.tree@.on_tree(self.locked_subtree@)
    }

    #[verifier::inline]
    pub open spec fn virt_addr_spec(self) -> usize {
        self.path.vaddr()
    }

    pub open spec fn push_level_spec(self) -> ConcreteCursor {
        ConcreteCursor {
            path: PageTableTreePathModel{
                inner: self.path.inner.push_tail(0 as usize),
            },
            ..self
        }
    }

    pub open spec fn pop_level_spec(self) -> ConcreteCursor {
        let (tail,popped) = self.path.inner.pop_tail();
        ConcreteCursor {
            path: PageTableTreePathModel{
                inner: popped
            },
            ..self
        }
    }

    pub proof fn lemma_pop_level_spec_preserves_vaddr(self, n:int)
        requires
            self.path.inner.len() == n,
            n > 0,
            self.path.inner.inv(),
            self.path.inner.0[n-1] == 0,
        ensures
            self.pop_level_spec().path.vaddr() == self.path.vaddr(),
    {
        let ghost orig = self.path.inner;
        let ghost popped = orig.pop_tail().1;
        assert(self.pop_level_spec().path.inner == popped);
        PageTableTreePathModel::rec_vaddr_pop_0(orig,n,0);
    }

    pub proof fn lemma_push_level_spec_preserves_vaddr(self, n:int)
        requires
            self.path.inner.len() == n,
            n < NR_LEVELS(),
            self.path.inner.inv(),
        ensures
            self.push_level_spec().path.vaddr() == self.path.vaddr(),
    {
        let ghost orig = self.path.inner;
        let ghost pushed = orig.push_tail(0 as usize);
        assert(self.push_level_spec().path.inner == pushed);
        PageTableTreePathModel::rec_vaddr_push_0(orig,n,0);
    }

    pub open spec fn inc_pop_aligned_rec(path:TreePath<CONST_NR_ENTRIES>) -> TreePath<CONST_NR_ENTRIES>
        decreases
            path.len(),
    {
        if path.len() == 0 {
            path
        } else {
            let n = path.len();
            let val = path.0[n - 1];
            let new_path = path.0.update(n - 1, (val + 1) as usize);

            if new_path[n-1] % NR_ENTRIES() == 0 {
                let (tail,popped) = path.pop_tail();
                Self::inc_pop_aligned_rec(popped)
            } else {
                path
            }
        }
    }

    pub open spec fn move_forward_spec(self) -> ConcreteCursor {
        ConcreteCursor {
            path: PageTableTreePathModel{
                inner: Self::inc_pop_aligned_rec(self.path.inner)
            },
            ..self
        }
    }

    pub open spec fn get_nodes(self, path: PageTableTreePathModel) ->
    (res: Seq<PageTableNodeValue>)
    recommends
        self.inv(),
        path.inv(),
    {
        self.tree@.trace(path@)
    }

}

}
