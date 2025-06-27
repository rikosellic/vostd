use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;

verus! {

pub proof fn lemma_usize_pow2_no_overflow(n: nat)
    requires
        n < usize::BITS,
    ensures
        0 < pow2(n) <= usize::MAX,
{
    lemma_pow2_pos(n);
    if usize::BITS == 32 {
        lemma_u32_pow2_no_overflow(n);
    } else if usize::BITS == 64 {
        lemma_u64_pow2_no_overflow(n);
    } else {
        assert(false);  // Unsupported usize size
    }
}

proof fn test(x: u64, shift: u64)
    requires
        0 <= shift < <u64>::BITS,
    ensures
        x * pow2(shift as nat) <= <u64>::MAX <==> x <= (<u64>::MAX >> shift),
{
    assert(<u64>::MAX >> shift == <u64>::MAX as nat / pow2(shift as nat)) by {
        lemma_u64_shr_is_div(<u64>::MAX, shift as u64);
    };

    admit();

}

} // verus!
