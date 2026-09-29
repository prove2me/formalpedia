-- Prove2me | solution 1 for BonferroniMarginals.sharp_bonferroni_defect_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:29:01.046976+00:00
-- url     : https://prove2.me/submissions/79bbbdcb-45c5-4f12-a6bd-6abfe085deaa

-- Sol generated from MachineLearning/BonferroniMarginals/SharpBonferroni.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability
import Theorems.Thm_BonferroniMarginals_one_le_mult_of_mem_cover
import Theorems.Thm_BonferroniMarginals_sum_mult_eq_sum_card
import Theorems.Thm_BonferroniMarginals_sum_offDiag_eq

/-!
# The sharp (unordered-pair) second Bonferroni inequality

`Core.lean` proves
`∑ᵢ|Aᵢ| ≤ |cover| + ∑_{(i,j) ∈ offDiag}|Aᵢ ∩ Aⱼ|`,
where the pair sum runs over *ordered* pairs and therefore counts every overlap
twice.  The classical second Bonferroni inequality is the unordered statement
`∑ᵢ|Aᵢ| − ∑_{i<j}|Aᵢ ∩ Aⱼ| ≤ |cover|`,
which is a factor `2` stronger on the correction term.  This file proves it in
the index-order-free form

`2·∑ᵢ|Aᵢ| ≤ 2·|cover| + ∑_{(i,j) ∈ offDiag}|Aᵢ ∩ Aⱼ|`

together with its exact defect and its tightness characterisation.

* `sharp_bonferroni_defect_identity` —
  `2·∑ᵢ|Aᵢ| + ∑ₓ (mult x − 1)(mult x − 2) = 2·|cover| + ∑_{i≠j}|Aᵢ ∩ Aⱼ|`.
  The defect is now the *second factorial* deviation of the multiplicity from
  the interval `{1, 2}`, rather than the squared deviation from `1`.
* `sharp_bonferroni` — the inequality.
* `sharp_bonferroni_tight_iff` — equality holds iff no point is covered three
  times, i.e. exactly on the families for which the double-collision bound
  `card_doubleCollision_mul_le` is also tight (`doubleCollision_tight_iff`).
  The two second-order inequalities of the machinery therefore have *the same*
  extremal class: multiplicity-`≤ 2` families.
* `sharp_bonferroni_strictly_stronger` — the sharp bound implies the
  `Core.lean` bound.

Machine-learning reading: the classical union-bound correction is exactly
lossless for ensembles in which no sample is misclassified by three or more
members; beyond that regime the correction over-counts, by a computable amount.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω] [DecidableEq ι]







open BonferroniMarginals in
theorem solution(I : Finset ι) (A : ι → Finset Ω) :
    2 * ∑ i ∈ I, (A i).card
        + ∑ x ∈ cover I A, (mult I A x - 1) * (mult I A x - 2)
      = 2 * (cover I A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by
  rw [sum_offDiag_eq, ← sum_mult_eq_sum_card, Finset.mul_sum, ← Finset.sum_add_distrib,
    show 2 * (cover I A).card = ∑ _x ∈ cover I A, 2 by
      rw [Finset.sum_const, smul_eq_mul, mul_comm],
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (one_le_mult_of_mem_cover hx)
  rw [hk, show 1 + k - 1 = k by omega]
  cases k with
  | zero => simp
  | succ n =>
    rw [show 1 + (n + 1) - 2 = n by omega]
    ring
