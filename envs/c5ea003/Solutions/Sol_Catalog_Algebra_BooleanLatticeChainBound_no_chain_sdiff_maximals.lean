-- Prove2me | solution 1 for Catalog.Algebra.BooleanLatticeChainBound.no_chain_sdiff_maximals
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:06:08.762229+00:00
-- url     : https://prove2.me/submissions/5b1ac984-110a-40d2-8209-76dc9a3d78a2

-- Sol generated from Algebra/BooleanLatticeChainBound.lean
import Mathlib
import Definitions.Def_Algebra_BooleanLatticeChainBound
/-
# Forbidden Boolean-lattice subposets: the chain bound and its sharpening

This file develops, from scratch, a formal framework for the extremal problem

  `La(n, B_d) = max { |F| : F ⊆ 2^[n], F contains no (weak) copy of the Boolean lattice B_d }`

and proves the classical *chain bound* `La(n, B_d) ≤ (2^d - 1) * C(n, ⌊n/2⌋)`
together with a number of complementary results relevant to the conjecture
`La(n, B_d) ≤ (d + c) * C(n, ⌊n/2⌋)` for an absolute constant `c`.

## Main definitions

* `HasBdCopy d F` : the family `F` of subsets of `Fin n` contains a *weak* copy of the
  `d`-dimensional Boolean lattice, i.e. an injective, containment-preserving map
  `Finset (Fin d) → F`.
* `BdFree d F`    : `F` contains no such copy.
* `HasChain k F`  : `F` contains a strictly increasing chain of `k` sets.
* `La n d`        : the extremal function, the supremum of `|F|` over `B_d`-free `F`.

## Main results

* `hasBdCopy_of_hasChain`    : a chain of `2^d` sets already yields a weak copy of `B_d`.
* `lubell_le_of_no_chain`    : the Lubell mass of a `(k+1)`-chain-free family is at most `k`
  (a Mirsky-type induction feeding into the LYM inequality). This is strictly stronger
  than the corresponding cardinality bound.
* `card_le_of_bdFree`        : the chain bound `|F| ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_le_chain_bound`        : `La n d ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_one`                   : `La n 1 = C(n, ⌊n/2⌋)` (Sperner's theorem, both directions).
* `La_le_height_bound`       : `La n d ≤ (n+1) * C(n, ⌊n/2⌋)`, hence the conjectured bound
  `(d + 1) * C(n, ⌊n/2⌋)` holds unconditionally whenever `n ≤ d`.
* `La_three_le_four_of_le_eight` : the conjectured `d = 3` bound `La n 3 ≤ 4 * C(n, ⌊n/2⌋)`
  holds for every `n ≤ 8`.
* `La_ge_consecutive_levels` : the lower bound coming from `d` consecutive levels,
  `La n d ≥ ∑_{i=a}^{a+d-1} C(n, i)`.
* `hasBdCopy_succ_of_stacked` and `hasBdCopy_succ_of_parallel_chains` : a *doubling*
  criterion showing that a `B_{d+1}` copy already arises from two "parallel" `B_d` copies,
  a configuration strictly weaker than a single long chain.
-/


open Catalog.Algebra.BooleanLatticeChainBound

open Finset

/-! ## The central binomial coefficient -/




/-! ## Weak copies of the Boolean lattice -/

variable {n : ℕ}





/-! ## A linear extension of `B d` -/






/-! ## Chains produce Boolean-lattice copies -/




/-! ## Mirsky + LYM : the Lubell mass of a chain-free family -/






/-- Every non-maximal member of a family sits strictly below some member. -/
lemma exists_gt_of_not_mem_maximals {F : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hA : A ∈ F) (hnot : A ∉ maximals F) : ∃ B ∈ F, A ⊂ B := by
  simp only [maximals, Finset.mem_filter, not_and, not_forall] at hnot
  obtain ⟨B, hB⟩ := hnot hA
  simp only [not_not] at hB
  exact ⟨B, hB.1, hB.2⟩

  




/-! ## The chain bound -/



/-! ## Chains in `2^[n]` have length at most `n+1` -/




/-! ## The extremal function `La` -/












/-! ## `d = 1` : Sperner's theorem -/



/-! ## Lower bounds from consecutive levels -/









/-! ## The conjecture for `d = 3` in small dimension -/





/-! ## A doubling criterion : `B (d+1)` copies from two parallel `B d` copies -/








open Catalog.Algebra.BooleanLatticeChainBound in
theorem solution{k : ℕ} {F : Finset (Finset (Fin n))}
    (h : ¬ HasChain (k + 2) F) : ¬ HasChain (k + 1) (F \ maximals F) := by
  rintro ⟨g, hmem, hg⟩
  have hgk : g k ∈ F \ maximals F := hmem k (Nat.lt_succ_self k)
  have hgkF : g k ∈ F := (Finset.mem_sdiff.1 hgk).1
  obtain ⟨B, hBF, hgB⟩ := exists_gt_of_not_mem_maximals hgkF (Finset.mem_sdiff.1 hgk).2
  refine h ⟨fun i => if i < k + 1 then g i else B, ?_, ?_⟩
  · intro i hi
    by_cases hik : i < k + 1
    · simpa [hik] using (Finset.mem_sdiff.1 (hmem i hik)).1
    · simpa [hik] using hBF
  · intro i j hij hj
    by_cases hjk : j < k + 1
    · have hik : i < k + 1 := lt_trans hij hjk
      simpa [hik, hjk] using hg i j hij hjk
    · have hik : i < k + 1 := by omega
      have hjB : ¬ j < k + 1 := hjk
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hik) with hik' | hik'
      · simpa [hik, hjB, hik'] using hgB
      · have : g i ⊂ g k := hg i k hik' (Nat.lt_succ_self k)
        simpa [hik, hjB] using this.trans hgB
