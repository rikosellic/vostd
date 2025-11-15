use vstd::prelude::*;
use vstd::map::*;
use vstd::set::*;

verus! {

broadcast use {
    group_map_axioms,
    group_set_axioms,
};

pub broadcast proof fn lemma_map_remove_keys_finite<K, V>(m: Map<K, V>, keys: Set<K>)
    requires
        m.dom().finite(),
        keys.finite(),
    ensures
        (#[trigger] m.remove_keys(keys)).dom().finite(),
{
    assert(m.remove_keys(keys).dom() =~= m.dom().difference(keys));
}

pub broadcast group group_map_extra_lemmas {
    lemma_map_remove_keys_finite,
}

} // verus!
