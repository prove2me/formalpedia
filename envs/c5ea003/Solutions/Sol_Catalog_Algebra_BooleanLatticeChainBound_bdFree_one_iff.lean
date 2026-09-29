-- Prove2me | solution 1 for Catalog.Algebra.BooleanLatticeChainBound.bdFree_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:50:49.203438+00:00
-- url     : https://prove2.me/submissions/f8e7f4bb-22a7-472a-8a60-8363a3f474e3

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







  




/-! ## The chain bound -/



/-! ## Chains in `2^[n]` have length at most `n+1` -/




/-! ## The extremal function `La` -/












/-! ## `d = 1` : Sperner's theorem -/



/-! ## Lower bounds from consecutive levels -/









/-! ## The conjecture for `d = 3` in small dimension -/





/-! ## A doubling criterion : `B (d+1)` copies from two parallel `B d` copies -/








open Catalog.Algebra.BooleanLatticeChainBound in
theorem solution{F : Finset (Finset (Fin n))} :
    BdFree 1 F ↔ IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) := by
  constructor
  · intro hfree A hA B hB hne hsub
    have hext : ∀ S T : Finset (Fin 1), ((0 : Fin 1) ∈ S ↔ (0 : Fin 1) ∈ T) → S = T := by
      intro S T hiff
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact hiff
    simp only [Finset.mem_coe] at hA hB
    refine hfree ⟨fun S => if (0 : Fin 1) ∈ S then B else A, ?_, ?_, ?_⟩
    · intro S T hST
      by_cases hS : (0 : Fin 1) ∈ S <;> by_cases hT : (0 : Fin 1) ∈ T <;>
        simp only [hS, hT, if_true, if_false] at hST
      · exact hext S T (by simp [hS, hT])
      · exact absurd hST.symm hne
      · exact absurd hST hne
      · exact hext S T (by simp [hS, hT])
    · intro S
      by_cases hS : (0 : Fin 1) ∈ S <;> simp [hS, hA, hB]
    · intro S T hST
      by_cases hS : (0 : Fin 1) ∈ S <;> by_cases hT : (0 : Fin 1) ∈ T <;>
        simp only [hS, hT, if_true, if_false]
      · exact subset_rfl
      · exact absurd (hST hS) hT
      · exact hsub
      · exact subset_rfl
  · rintro h ⟨f, hinj, hmem, hmono⟩
    have hne : f ∅ ≠ f {0} := fun hEq => by simpa using hinj hEq
    exact h (hmem ∅) (hmem {0}) hne (hmono _ _ (Finset.empty_subset _))
