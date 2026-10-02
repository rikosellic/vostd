/// Virtual-address manipulation specs and lemmas for `CursorOwner`.
///
/// This module contains:
/// - Spec functions for zeroing VA indices below the cursor's level
///   (`zero_below_level`).
/// - Lemmas about how zeroing preserves fields other than VA.
/// - Spec functions for the cursor's current VA and VA range
///   (`cur_va`, `cur_va_range`).
/// - Lemmas relating the abstract VA to the page table view range.
/// - Specifications and proofs for repositioning the cursor inside its current node.
use vstd::prelude::*;
use vstd_extra::{arithmetic::nat_align_down, ghost_tree::*, ownership::*};

use crate::specs::{
    arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::page_table::{
        AbstractVaddr, Mapping,
        cursor::{
            owners::{CursorContinuation, CursorOwner},
            page_size_lemmas::{
                lemma_page_size_divides, lemma_page_size_ge_page_size, lemma_page_size_spec_values,
            },
        },
        lemma_page_size_for_level_matches_page_size, lemma_pte_index_spec_matches_abstract,
        lemma_vaddr_upper_bits_spec_matches_abstract,
        owners::*,
        page_size_for_level_spec, pte_index_spec, vaddr_upper_bits_spec,
    },
};

use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_size, page_table::*};
use crate::specs::task::InAtomicMode;
use core::ops::Range;

verus! {

broadcast use {
    group_ghost_tree_lemmas,
    AbstractVaddr::from_vaddr_to_vaddr_roundtrip,
    AbstractVaddr::reflect_from_vaddr,
};

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    pub open spec fn zero_below_level(self) -> Self
        recommends
            1 <= self.level <= C::NR_LEVELS(),
    {
        Self {
            va: nat_align_down(
                self.va as nat,
                page_size_for_level_spec::<C>(self.level) as nat,
            ) as Vaddr,
            ..self
        }
    }

    pub open spec fn cur_va(self) -> Vaddr {
        self.va
    }

    /// Temporary decomposition of the numeric current address for the remaining legacy proofs.
    pub open spec fn va_view(self) -> AbstractVaddr {
        AbstractVaddr::from_vaddr(self.va)
    }

    pub open spec fn prefix_vaddr(self) -> Vaddr {
        self.prefix
    }

    /// Temporary decomposition of the numeric prefix for the remaining legacy proofs.
    pub open spec fn prefix_view(self) -> AbstractVaddr {
        AbstractVaddr::from_vaddr(self.prefix)
    }

    pub open spec fn cur_va_range(self) -> Range<Vaddr> {
        let size = page_size(self.level);
        let start = nat_align_down(self.cur_va() as nat, size as nat) as Vaddr;
        Range { start, end: (start + size) as Vaddr }
    }

    pub open spec fn set_va_in_node(self, new_va: Vaddr) -> Self {
        let old_cont = self.continuations[self.level - 1];
        Self {
            va: new_va,
            continuations: self.continuations.insert(
                self.level - 1,
                CursorContinuation { idx: pte_index_spec::<C>(new_va, self.level), ..old_cont },
            ),
            // Repositioning to a concrete in-range VA clears the
            // transient `popped_too_high` state.
            popped_too_high: false,
            ..self
        }
    }

    /// Compatibility lemma for proofs that still use the decomposed address view.
    pub proof fn lemma_zero_below_level_view(self)
        requires
            1 <= self.level <= C::NR_LEVELS(),
        ensures
            self.zero_below_level().va_view() == self.va_view().align_down(self.level as int),
            self.zero_below_level().va
                == nat_align_down(self.va as nat, page_size(self.level) as nat) as Vaddr,
    {
        C::lemma_paging_consts_properties();
        AbstractVaddr::from_vaddr_wf(self.va);
        lemma_page_size_for_level_matches_page_size::<C>(self.level);
        self.va_view().align_down_to_vaddr_nat_align_down(self.level as int);
        self.va_view().align_down_inv(self.level as int);
        AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va_view().align_down(self.level as int));
    }

    pub proof fn do_zero_below_level(tracked &mut self)
        requires
            old(self).inv(),
            old(self).level <= old(self).guard_level,
        ensures
            *final(self) == old(self).zero_below_level(),
            final(self).inv(),
    {
        let ghost old_self = *self;
        C::lemma_paging_consts_properties();
        old_self.lemma_zero_below_level_view();
        old_self.va_view().align_down_shape(old_self.level as int);
        old_self.va_view().align_down_leading_bits(old_self.level as int);
        self.va = old_self.zero_below_level().va;

        old_self.lemma_locked_range_span();
        lemma_page_size_ge_page_size(old_self.level as PagingLevel);
        lemma_page_size_ge_page_size(old_self.guard_level as PagingLevel);
        lemma_page_size_divides(old_self.level as PagingLevel, old_self.guard_level as PagingLevel);
        old_self.va_view().align_down_to_vaddr_nat_align_down(old_self.level as int);

        let ghost old_va_val = old_self.va_view().to_vaddr() as nat;
        let ghost prefix_va_val = old_self.prefix_view().to_vaddr() as nat;
        let ghost ps = page_size(old_self.level as PagingLevel) as nat;
        let ghost guard_ps = page_size(old_self.guard_level as PagingLevel) as nat;
        let ghost start = old_self.locked_range().start as nat;

        vstd_extra::arithmetic::lemma_nat_align_down_monotone(prefix_va_val, ps, guard_ps);
        vstd_extra::arithmetic::lemma_mod_0_add(start as int, guard_ps as int, ps as int);

        vstd_extra::arithmetic::lemma_nat_align_down_sound(old_va_val, ps);
        if !self.popped_too_high && (self.in_locked_range() || self.level < self.guard_level) {
            if self.level == self.guard_level {
                let new_va_val = self.va_view().to_vaddr() as nat;
                let diff = (new_va_val - start) as nat;
                vstd::arithmetic::div_mod::lemma_mod_equivalence(
                    new_va_val as int,
                    start as int,
                    ps as int,
                );
                vstd::arithmetic::div_mod::lemma_small_mod(diff, ps);
            }
        }
    }

    pub proof fn zero_preserves_all_but_va(self)
        ensures
            self.zero_below_level().level == self.level,
            self.zero_below_level().continuations == self.continuations,
            self.zero_below_level().guard_level == self.guard_level,
            self.zero_below_level().prefix == self.prefix,
            self.zero_below_level().popped_too_high == self.popped_too_high,
    {
    }

    pub proof fn inc_and_zero_increases_va(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().zero_below_level().va_view().to_vaddr() > self.va_view().to_vaddr(),
    {
        // inc_index increments va.index[level-1] by 1. zero_below_level zeroes
        // indices below level (= align_down). The result is align_up(va, ps).
        self.lemma_inc_index_va_view();
        let inc = self.inc_index();
        C::lemma_paging_consts_properties();
        inc.lemma_zero_below_level_view();
        inc.zero_preserves_all_but_va();
        assert(inc.va_view().inv());

        let ps = page_size(self.level as PagingLevel) as nat;
        let self_va = self.va_view().to_vaddr() as nat;
        lemma_page_size_ge_page_size(self.level as PagingLevel);

        // Step 1: inc_index adds page_size to the vaddr.
        self.va_view().index_increment_adds_page_size(self.level as int);
        let inc_va = inc.va_view().to_vaddr() as nat;

        // Step 2: zero_below_level().va == inc.va_view().align_down(level).
        // align_down_concrete gives .reflect(nat_align_down(inc_va, ps)).
        inc.va_view().align_down_concrete(self.level as int);
        let new_va = vstd_extra::arithmetic::nat_align_down(inc_va, ps);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(inc_va, ps);
        assert(new_va <= usize::MAX);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(new_va as Vaddr);
        // Now inc.zero_below_level().va_view().to_vaddr() == new_va.

        // Step 3: align_down(self_va + ps, ps) = align_down(self_va, ps) + ps.
        // Because (self_va + ps) % ps == self_va % ps, adding a full ps doesn't
        // change the remainder.
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(self_va as int, ps as int);

        // Step 4: align_down(self_va, ps) + ps > self_va.
        // Because align_down(self_va, ps) = self_va - self_va % ps,
        // and self_va % ps < ps.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(self_va as int, ps as int);
    }

    /// The current virtual address falls within the VA range of the
    /// current subtree's path, in canonical form (positional vaddr plus
    /// the `leading_bits * 2^48` shift).
    pub proof fn cur_va_in_subtree_range(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            vaddr(self.cur_subtree().value().path) + self.va_view().leading_bits * 0x1_0000_0000_0000int
                <= self.cur_va(),
            self.cur_va() < vaddr(self.cur_subtree().value().path) + self.va_view().leading_bits
                * 0x1_0000_0000_0000int + page_size(self.level as PagingLevel),
    {
        let L = self.level as int;
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(self.va);
        let cont = self.continuations[L - 1];
        let subtree_path = cont.path().push_tail(cont.idx as int);
        let va_path = self.va_view().to_path(L - 1);

        self.va_view().to_path_len(L - 1);

        assert forall|i: int| 0 <= i < subtree_path.len() implies subtree_path[i] == va_path[i] by {
            self.va_view().to_path_index(L - 1, i);
        };

        self.va_view().to_path_inv(L - 1);
        self.lemma_cur_subtree_inv();
        AbstractVaddr::rec_vaddr_eq_if_indices_eq(subtree_path, va_path, 0);
        self.va_view().vaddr_range_from_path(L - 1);
    }

    proof fn lemma_locked_range_vaddr_prefix_match_abstract(self, new_va: Vaddr)
        requires
            self.inv(),
            new_va % PAGE_SIZE == 0,
            AbstractVaddr::from_vaddr(new_va).leading_bits == self.prefix_view().leading_bits,
            self.locked_range().start <= new_va < self.locked_range().end,
        ensures
            forall|i: int|
                #![trigger AbstractVaddr::from_vaddr(new_va).index[i]]
                self.guard_level - 1 <= i < NR_LEVELS ==> AbstractVaddr::from_vaddr(new_va).index[i]
                    == self.prefix_view().index[i],
    {
        let gl = self.guard_level;
        let start = self.locked_range().start;
        let prefix_val = self.prefix_view().to_vaddr();

        self.lemma_prefix_aligned_to_guard_level();
        self.lemma_prefix_plus_ps_no_overflow();
        self.prefix_view().aligned_align_down_is_self(gl as int);
        self.prefix_view().aligned_align_up_advances(gl as int);

        lemma_page_size_spec_values();
        if gl == 1 {
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix_view());
        } else {
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix_view());
            AbstractVaddr::same_node_indices_match(
                new_va,
                prefix_val,
                start,
                (gl - 1) as PagingLevel,
            );
        }
    }

    pub proof fn lemma_locked_range_vaddr_prefix_match(self, new_va: Vaddr)
        requires
            self.inv(),
            new_va % C::BASE_PAGE_SIZE() == 0,
            vaddr_upper_bits_spec::<C>(new_va)
                == vaddr_upper_bits_spec::<C>(self.prefix_vaddr()),
            self.locked_range().start <= new_va < self.locked_range().end,
        ensures
            forall|i: int|
                self.guard_level - 1 <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                    new_va,
                    (i + 1) as PagingLevel,
                )) == pte_index_spec::<C>(self.prefix_vaddr(), (i + 1) as PagingLevel),
    {
        let prefix_val = self.prefix_view().to_vaddr();

        C::lemma_paging_consts_properties();
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(self.prefix);
        self.prefix_view().reflect_to_vaddr();
        lemma_vaddr_upper_bits_spec_matches_abstract::<C>(new_va);
        lemma_vaddr_upper_bits_spec_matches_abstract::<C>(prefix_val);

        self.lemma_locked_range_vaddr_prefix_match_abstract(new_va);

        assert forall|i: int| self.guard_level - 1 <= i < C::NR_LEVELS() implies (
        #[trigger] pte_index_spec::<C>(new_va, (i + 1) as PagingLevel)) == pte_index_spec::<C>(
            prefix_val,
            (i + 1) as PagingLevel,
        ) by {
            lemma_pte_index_spec_matches_abstract::<C>(new_va, (i + 1) as PagingLevel);
            lemma_pte_index_spec_matches_abstract::<C>(prefix_val, (i + 1) as PagingLevel);
        };
    }

    /// The entry selected by the cursor's concrete VA is the entry owned by its current
    /// continuation. This is the architecture-parameterized replacement for exposing the
    /// decomposed address stored in `CursorOwner`.
    pub proof fn lemma_cur_pte_index(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            1 <= self.level <= C::NR_LEVELS(),
            pte_index_spec::<C>(self.cur_va(), self.level)
                == self.continuations[self.level - 1].idx,
            pte_index_spec::<C>(self.cur_va(), self.level) < NR_ENTRIES,
    {
        C::lemma_paging_consts_properties();
        self.va_view().reflect_to_vaddr();
        lemma_pte_index_spec_matches_abstract::<C>(self.cur_va(), self.level);
    }

    /// Architecture-parameterized entry point for repositioning a cursor inside its current
    /// page-table node.
    pub proof fn tracked_set_vaddr_in_node(tracked &mut self, new_va: Vaddr)
        requires
            old(self).inv(),
            new_va % C::BASE_PAGE_SIZE() == 0,
            vaddr_upper_bits_spec::<C>(new_va) == vaddr_upper_bits_spec::<C>(old(self).cur_va()),
            forall|i: int|
                old(self).level <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                    new_va,
                    (i + 1) as PagingLevel,
                )) == pte_index_spec::<C>(old(self).cur_va(), (i + 1) as PagingLevel),
            old(self).locked_range().start <= new_va < old(self).locked_range().end,
            old(self).level <= old(self).guard_level,
        ensures
            *final(self) == old(self).set_va_in_node(new_va),
            final(self).inv(),
    {
        let ghost old_self = *self;

        C::lemma_paging_consts_properties();
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(old_self.prefix);
        lemma_pte_index_spec_matches_abstract::<C>(new_va, old_self.level);
        old_self.va_view().reflect_to_vaddr();

        lemma_vaddr_upper_bits_spec_matches_abstract::<C>(new_va);
        lemma_vaddr_upper_bits_spec_matches_abstract::<C>(old_self.cur_va());
        old_self.prefix_view().reflect_to_vaddr();
        lemma_vaddr_upper_bits_spec_matches_abstract::<C>(old_self.prefix_view().to_vaddr());

        assert(vaddr_upper_bits_spec::<C>(new_va)
            == vaddr_upper_bits_spec::<C>(old_self.prefix_view().to_vaddr()));

        assert forall|i: int| old_self.level <= i < C::NR_LEVELS() implies (
        #[trigger] AbstractVaddr::from_vaddr(new_va).index[i]) == old_self.va_view().index[i] by {
            lemma_pte_index_spec_matches_abstract::<C>(new_va, (i + 1) as PagingLevel);
            lemma_pte_index_spec_matches_abstract::<C>(old_self.cur_va(), (i + 1) as PagingLevel);
        };

        let ghost new_abs_va = AbstractVaddr::from_vaddr(new_va);
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);

        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(new_va);

        cont.idx = pte_index_spec::<C>(new_va, old_self.level);

        self.continuations.tracked_insert(self.level - 1, cont);
        self.va = new_va;
        self.popped_too_high = false;

        assert(self.continuations == old_self.continuations.insert(old_self.level - 1, cont));

        old_self.lemma_locked_range_vaddr_prefix_match(new_va);

        assert forall|i: int| old_self.guard_level - 1 <= i < C::NR_LEVELS() implies (
        #[trigger] AbstractVaddr::from_vaddr(new_va).index[i]) == old_self.prefix_view().index[i] by {
            assert(pte_index_spec::<C>(new_va, (i + 1) as PagingLevel)
                == pte_index_spec::<C>(old_self.prefix_view().to_vaddr(), (i + 1) as PagingLevel));
            lemma_pte_index_spec_matches_abstract::<C>(new_va, (i + 1) as PagingLevel);
            lemma_pte_index_spec_matches_abstract::<C>(old_self.prefix_view().to_vaddr(), (i + 1) as PagingLevel);
        };

        if old_self.level < old_self.guard_level {
            old_self.lemma_prefix_in_locked_range();
        }
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    /// Connects the executable cursor address to the architecture-parameterized index owned by
    /// its ghost continuation, without exposing the owner's decomposed address representation.
    pub proof fn lemma_pte_index_matches_owner(self, owner: CursorOwner<'rcu, C>)
        requires
            self.wf(owner),
            owner.inv(),
            owner.in_locked_range(),
        ensures
            1 <= self.level <= C::NR_LEVELS(),
            pte_index_spec::<C>(self.va, self.level)
                == owner.continuations[owner.level - 1].idx,
            pte_index_spec::<C>(self.va, self.level) < NR_ENTRIES,
    {
        owner.lemma_cur_pte_index();
    }
}

} // verus!
