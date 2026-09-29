-- Prove2me | solution 1 for BonferroniMarginals.sharp_bonferroni_tight_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:30:54.44419+00:00
-- url     : https://prove2.me/submissions/7db300af-62b3-4847-baba-f26b947afd85

-- Sol generated from MachineLearning/BonferroniMarginals/SharpBonferroni.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability
import Theorems.Thm_BonferroniMarginals_one_le_mult_of_mem_cover
import Theorems.Thm_BonferroniMarginals_sharp_bonferroni_defect_identity

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
    (2 * ∑ i ∈ I, (A i).card
        = 2 * (cover I A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card)
      ↔ ∀ x ∈ cover I A, mult I A x ≤ 2 := by
  have hid := sharp_bonferroni_defect_identity I A
  constructor
  · intro heq
    have hzero : ∑ x ∈ cover I A, (mult I A x - 1) * (mult I A x - 2) = 0 := by omega
    intro x hx
    have hterm := (Finset.sum_eq_zero_iff.mp hzero) x hx
    have h1 := one_le_mult_of_mem_cover hx
    rcases Nat.mul_eq_zero.mp hterm with h | h <;> omega
  · intro hle
    have hzero : ∑ x ∈ cover I A, (mult I A x - 1) * (mult I A x - 2) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have := hle x hx
      have h2 : mult I A x - 2 = 0 := by omega
      rw [h2, mul_zero]
    omega
