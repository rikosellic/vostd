use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

use crate::arch::mm::PagingConsts;
use crate::mm::{PagingConstsTrait, PagingLevel};
use crate::mm::{ Paddr, Vaddr, nr_subpage_per_huge, page_size};
use crate::specs::arch::*;

verus! {

/// page_size::<C>(1) == C::BASE_PAGE_SIZE.
pub proof fn lemma_page_size_spec_level1<C: PagingConstsTrait>()
    ensures
        page_size::<C>(1) == C::BASE_PAGE_SIZE(),
{
    vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
        nr_subpage_per_huge::<C>().ilog2() as int,
    );
    broadcast use vstd::arithmetic::power2::lemma_pow2;

    vstd::arithmetic::power::lemma_pow0(2int);
}

/// When `va` is aligned to `page_size::<C>(large_level)` and `level <= large_level`, 
/// then `va` is aligned to page_size::<C>(level).
pub proof fn lemma_va_align_page_size<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
        va % C::BASE_PAGE_SIZE() == 0,
        exists|large_level: PagingLevel|
            1 <= large_level <= C::NR_LEVELS() + 1 && level <= large_level && va % page_size::<C>(
                large_level,
            ) == 0,
    ensures
        va % page_size::<C>(level) == 0,
{
    let large_level: PagingLevel = choose|l: PagingLevel|
        1 <= l <= C::NR_LEVELS() + 1 && level <= l && va % page_size::<C>(l) == 0;
    if level == 1nat {
        lemma_page_size_spec_level1::<C>();
    } else {
        let ps_l = page_size::<C>(level) as int;
        let ps_ll = page_size::<C>(large_level) as int;
        lemma_page_size_ge_page_size::<C>(level);
        lemma_page_size_ge_page_size::<C>(large_level);
        lemma_page_size_divides::<C>(level, large_level);
        assert(ps_ll >= ps_l) by {
            if ps_ll < ps_l {
                vstd::arithmetic::div_mod::lemma_small_mod(ps_ll as nat, ps_l as nat);
            }
        };
        let k = ps_ll / ps_l;
        vstd::arithmetic::div_mod::lemma_div_non_zero(ps_ll, ps_l);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps_ll, ps_l);
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, ps_l, k);
        assert(va as int % ps_l == 0);
    }
}

pub proof fn lemma_va_align_page_size_level_1<C: PagingConstsTrait>(va: Vaddr)
    requires
        va % C::BASE_PAGE_SIZE() == 0,
    ensures
        va % page_size::<C>(1) == 0,
{
    lemma_page_size_spec_level1::<C>();
}

/// For any level in [1, C::NR_LEVELS], page_size::<C>(level) is a multiple of C::BASE_PAGE_SIZE.
pub proof fn lemma_page_size_multiple_of_page_size<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size::<C>(level) % C::BASE_PAGE_SIZE() == 0,
{
    lemma_page_size_spec_values::<C>();
}

/// For any level in [1, C::NR_LEVELS+1], the page size is at least C::BASE_PAGE_SIZE.
#[verifier::spinoff_prover]
pub proof fn lemma_page_size_ge_page_size<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        page_size::<C>(level) >= C::BASE_PAGE_SIZE(),
{
    lemma_page_size_spec_values::<C>();
}

/// `page_size` is monotone in the level: a higher level has a larger or equal page size.
/// This follows from page_size(level) = PAGE_SIZE * 512^(level-1); incrementing level multiplies
/// by 512, so page_size(l+1) = 512 * page_size(l) > page_size(l).
pub proof fn lemma_page_size_monotone<C: PagingConstsTrait>(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= C::NR_LEVELS() + 1,
        1 <= l2 <= C::NR_LEVELS() + 1,
        l1 <= l2,
    ensures
        page_size::<C>(l1) <= page_size::<C>(l2),
{
    if l1 != l2 {
        let ps1 = page_size::<C>(l1);
        let ps2 = page_size::<C>(l2);

        lemma_page_size_ge_page_size::<C>(l1);
        lemma_page_size_ge_page_size::<C>(l2);
        lemma_page_size_divides::<C>(l1, l2);

        assert(ps1 <= ps2) by {
            if ps2 < ps1 {
                vstd::arithmetic::div_mod::lemma_small_mod(ps2 as nat, ps1 as nat);
            }
        };
    }
}

/// `(page_size(level) / PAGE_SIZE) * PAGE_SIZE == page_size(level)` for level in [1, NR_LEVELS+1].
/// page_size(level) is divisible by PAGE_SIZE so the integer division is exact.
pub proof fn lemma_page_size_div_mul_eq<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        (page_size::<C>(level) / C::BASE_PAGE_SIZE()) * C::BASE_PAGE_SIZE() == page_size::<C>(level),
{
    admit();
}

/// `NR_ENTRIES * page_size(level - 1) == page_size(level)` for level in [2, NR_LEVELS + 1].
/// A huge page at `level` consists of NR_ENTRIES sub-pages each of size `page_size(level - 1)`.
pub proof fn lemma_nr_entries_times_sub_page_size<C: PagingConstsTrait>(level: PagingLevel)
    requires
        2 <= level <= C::NR_LEVELS() + 1,
    ensures
        C::NR_ENTRIES() as int * page_size::<C>((level - 1) as PagingLevel) as int
            == page_size::<C>(level) as int,
{
    lemma_page_size_spec_values::<C>();
    lemma_nr_subpage_per_huge_eq_nr_entries();
}

pub proof fn lemma_split_sub_page_big_j<C:PagingConstsTrait>(pa: Paddr, level: PagingLevel, i: usize) -> (big_j: usize)
    requires
        2 <= level <= C::NR_LEVELS(),
        0 < i < nr_subpage_per_huge::<C>(),
    ensures
        0 < big_j < page_size::<C>(level) / C::BASE_PAGE_SIZE(),
        (pa + i * page_size::<C>((level - 1) as PagingLevel)) as int == pa as int + big_j as int
            * C::BASE_PAGE_SIZE() as int,
        big_j as int == i as int * (page_size::<C>((level - 1) as PagingLevel) / C::BASE_PAGE_SIZE()) as int,
{
    let sub_pages_per_entry: int = (page_size::<C>((level - 1) as PagingLevel) / C::BASE_PAGE_SIZE()) as int;
    let big_j_int: int = i as int * sub_pages_per_entry;
    lemma_page_size_spec_values::<C>();
    lemma_page_size_div_mul_eq::<C>((level - 1) as PagingLevel);
    lemma_page_size_div_mul_eq::<C>(level);
    lemma_nr_entries_times_sub_page_size::<C>(level);
    vstd::arithmetic::mul::lemma_mul_strictly_positive(i as int, sub_pages_per_entry);
    vstd::arithmetic::mul::lemma_mul_strict_inequality(
        i as int,
        C::BASE_PAGE_SIZE()/C::PTE_SIZE() as int,
        sub_pages_per_entry,
    );
    vstd::arithmetic::mul::lemma_mul_is_associative(
        C::BASE_PAGE_SIZE()/C::PTE_SIZE() as int,
        sub_pages_per_entry,
        C::BASE_PAGE_SIZE() as int,
    );
    vstd::arithmetic::div_mod::lemma_div_by_multiple(
        C::BASE_PAGE_SIZE()/C::PTE_SIZE() as int * sub_pages_per_entry,
        C::BASE_PAGE_SIZE() as int,
    );
    vstd::arithmetic::mul::lemma_mul_is_associative(
        i as int,
        sub_pages_per_entry,
        C::BASE_PAGE_SIZE() as int,
    );
    big_j_int as usize
}

/// page_size(l2) is divisible by page_size(l1) when l1 <= l2.
pub proof fn lemma_page_size_divides<C:PagingConstsTrait>(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= l2 <= C::NR_LEVELS() + 1,
    ensures
        page_size::<C>(l2) % page_size::<C>(l1) == 0,
{
    admit();
}

} // verus!
