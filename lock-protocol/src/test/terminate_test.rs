use vstd::prelude::*;

verus! {
    pub open spec fn rc_greater_or_equal(nid: nat, rc: nat, cursors: Set<int>) -> bool
        decreases cursors.len(),
        when rc == 0 via just_terminate
    {
        if rc == 0 { false }
        else if cursors.len() == 0 { true }
        else {
            let cursor = cursors.choose();
            if (nid > 100) {
                rc_greater_or_equal(nid, rc, cursors.remove(cursor))
            } else {
                rc_greater_or_equal(nid, (rc - 1) as nat, cursors.remove(cursor))
            }
        }
    }

    #[via_fn]
    proof fn just_terminate(nid: nat, rc: nat, cursors: Set<int>) { // proof 
    }
}