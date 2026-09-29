-- Prove2me | solution 1 for Catalog.Algebra.BooleanLatticeChainBound.chain_comp_rank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:50:50.807978+00:00
-- url     : https://prove2.me/submissions/6488e679-afb7-4abf-ac40-d793c6374675

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



lemma rank_lt (d : ℕ) (S : Finset (Fin d)) : rank d S < 2 ^ d :=
  Fin.is_lt _

lemma rank_injective (d : ℕ) : Function.Injective (rank d) := by
  intro a b hab
  have h : (monoEquivOfFin (LinearExtension (Finset (Fin d)))
      (by show Fintype.card (Finset (Fin d)) = 2 ^ d; simp)).symm (toLinearExtension a)
      = (monoEquivOfFin (LinearExtension (Finset (Fin d)))
      (by show Fintype.card (Finset (Fin d)) = 2 ^ d; simp)).symm (toLinearExtension b) :=
    Fin.ext hab
  exact (OrderIso.injective _ h : (toLinearExtension a) = toLinearExtension b)

lemma rank_mono (d : ℕ) {S T : Finset (Fin d)} (h : S ⊆ T) : rank d S ≤ rank d T := by
  have : (monoEquivOfFin (LinearExtension (Finset (Fin d)))
      (by show Fintype.card (Finset (Fin d)) = 2 ^ d; simp)).symm (toLinearExtension S)
      ≤ (monoEquivOfFin (LinearExtension (Finset (Fin d)))
      (by show Fintype.card (Finset (Fin d)) = 2 ^ d; simp)).symm (toLinearExtension T) :=
    OrderIso.monotone _ (toLinearExtension.monotone h)
  exact this

/-! ## Chains produce Boolean-lattice copies -/




/-! ## Mirsky + LYM : the Lubell mass of a chain-free family -/







  




/-! ## The chain bound -/



/-! ## Chains in `2^[n]` have length at most `n+1` -/




/-! ## The extremal function `La` -/












/-! ## `d = 1` : Sperner's theorem -/



/-! ## Lower bounds from consecutive levels -/









/-! ## The conjecture for `d = 3` in small dimension -/





/-! ## A doubling criterion : `B (d+1)` copies from two parallel `B d` copies -/








open Catalog.Algebra.BooleanLatticeChainBound in
theorem solution{d : ℕ} {g : ℕ → Finset (Fin n)}
    (hg : ∀ i j, i < j → j < 2 ^ d → g i ⊂ g j) :
    Function.Injective (fun S : Finset (Fin d) => g (rank d S)) ∧
      ∀ S T : Finset (Fin d), S ⊆ T → g (rank d S) ⊆ g (rank d T) := by
  constructor
  · intro S T hST
    by_contra hne
    rcases lt_trichotomy (rank d S) (rank d T) with h | h | h
    · exact (Finset.ssubset_iff_subset_ne.1 (hg _ _ h (rank_lt d T))).2 hST
    · exact hne (rank_injective d h)
    · exact (Finset.ssubset_iff_subset_ne.1 (hg _ _ h (rank_lt d S))).2 hST.symm
  · intro S T hST
    rcases eq_or_lt_of_le (rank_mono d hST) with h | h
    · rw [h]
    · exact (Finset.ssubset_iff_subset_ne.1 (hg _ _ h (rank_lt d T))).1
