use vstd::prelude::*;

verus! {

pub broadcast proof fn lemma_map_remove_keys_finite<K, V>(m: Map<K, V>, keys: Set<K>)
    requires
        m.dom().finite(),
        keys.finite(),
    ensures
        (#[trigger] m.remove_keys(keys)).dom().finite(),
{
    broadcast use vstd::set::axiom_set_difference_finite;

    assert(m.remove_keys(keys).dom() =~= m.dom().difference(keys));
}

} // verus!
