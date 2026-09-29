-- Prove2me | solution 1 for Catalog.Algebra.BooleanLatticeChainBound.lubell_le_of_no_chain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:53:25.580022+00:00
-- url     : https://prove2.me/submissions/0f2e3790-b5c1-4ada-afee-67e56ca07798

-- Sol generated from Algebra/BooleanLatticeChainBound.lean
import Mathlib
import Definitions.Def_Algebra_BooleanLatticeChainBound
import Theorems.Thm_Catalog_Algebra_BooleanLatticeChainBound_no_chain_sdiff_maximals
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



lemma maximals_subset (F : Finset (Finset (Fin n))) : maximals F ⊆ F :=
  Finset.filter_subset _ _

lemma isAntichain_maximals (F : Finset (Finset (Fin n))) :
    IsAntichain (· ⊆ ·) ((maximals F : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
  intro A hA B hB hne hsub
  simp only [maximals, Finset.coe_filter, Set.mem_setOf_eq] at hA hB
  exact hA.2 B hB.1 (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)

lemma lubell_maximals_le_one (F : Finset (Finset (Fin n))) : lubell (maximals F) ≤ 1 := by
  have h := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℝ)
    (isAntichain_maximals F)
  simpa [lubell, Fintype.card_fin] using h


  




/-! ## The chain bound -/



/-! ## Chains in `2^[n]` have length at most `n+1` -/




/-! ## The extremal function `La` -/












/-! ## `d = 1` : Sperner's theorem -/



/-! ## Lower bounds from consecutive levels -/









/-! ## The conjecture for `d = 3` in small dimension -/





/-! ## A doubling criterion : `B (d+1)` copies from two parallel `B d` copies -/








open Catalog.Algebra.BooleanLatticeChainBound in
theorem solution:
    ∀ (k : ℕ) (F : Finset (Finset (Fin n))), ¬ HasChain (k + 1) F → lubell F ≤ k := by
  intro k
  induction k with
  | zero =>
    intro F hF
    have hempty : F = ∅ := by
      by_contra hne
      obtain ⟨A, hA⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact hF ⟨fun _ => A, fun i _ => hA, by omega⟩
    simp [lubell, hempty]
  | succ k ih =>
    intro F hF
    have hsub : maximals F ⊆ F := maximals_subset F
    have hsplit : lubell (F \ maximals F) + lubell (maximals F) = lubell F := by
      simpa [lubell] using
        (Finset.sum_sdiff (f := fun A : Finset (Fin n) => ((n.choose A.card : ℝ))⁻¹) hsub)
    have h1 : lubell (F \ maximals F) ≤ k := ih _ (no_chain_sdiff_maximals hF)
    have h2 : lubell (maximals F) ≤ 1 := lubell_maximals_le_one F
    have := add_le_add h1 h2
    rw [hsplit] at this
    push_cast
    linarith
