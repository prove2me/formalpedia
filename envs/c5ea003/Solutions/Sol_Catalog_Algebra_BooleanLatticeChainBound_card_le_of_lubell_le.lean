-- Prove2me | solution 1 for Catalog.Algebra.BooleanLatticeChainBound.card_le_of_lubell_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:50:49.838464+00:00
-- url     : https://prove2.me/submissions/a432b983-17e2-4671-8f5b-3f754daea152

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


lemma central_pos (n : ℕ) : 0 < central n := Nat.choose_pos (Nat.div_le_self _ _)

lemma choose_le_central (n r : ℕ) : n.choose r ≤ central n := Nat.choose_le_middle r n

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
theorem solution{F : Finset (Finset (Fin n))} {k : ℕ} (h : lubell F ≤ k) :
    F.card ≤ k * central n := by
  have hc : (0 : ℝ) < central n := by exact_mod_cast central_pos n
  have hterm : ∀ A ∈ F, ((central n : ℝ))⁻¹ ≤ ((n.choose A.card : ℝ))⁻¹ := by
    intro A _
    have h1 : (0 : ℝ) < n.choose A.card := by
      have : 0 < n.choose A.card := Nat.choose_pos (by simpa using A.card_le_univ)
      exact_mod_cast this
    have h2 : (n.choose A.card : ℝ) ≤ central n := by exact_mod_cast choose_le_central n A.card
    have := one_div_le_one_div_of_le h1 h2
    simpa [one_div] using this
  have hsum : (F.card : ℝ) * ((central n : ℝ))⁻¹ ≤ lubell F := by
    have := Finset.sum_le_sum hterm
    simpa [lubell, Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have : (F.card : ℝ) ≤ k * central n := by
    have h' : (F.card : ℝ) * ((central n : ℝ))⁻¹ ≤ k := le_trans hsum h
    calc (F.card : ℝ) = ((F.card : ℝ) * ((central n : ℝ))⁻¹) * central n := by
            field_simp
      _ ≤ (k : ℝ) * central n := by nlinarith
  exact_mod_cast this
