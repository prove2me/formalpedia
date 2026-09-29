-- Prove2me | solution 1 for TropicalLA.tdet_transpose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:59.429527+00:00
-- url     : https://prove2.me/submissions/f7010c6e-e79d-4ff2-8f0e-4c07f088c798

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_permWeight_le_tdet
/-
# The tropical determinant

Over the max-plus semiring the determinant of `A` (there being no signs) is

  `tdet A = max_{σ ∈ S_ι} Σ_i A i (σ i)`,

i.e. the value of the **optimal assignment problem** for the weight matrix `A`.

Main results:

* `tdet_isGreatest` : the tropical determinant *is* the weight of a maximum-weight
  permutation, and that maximum is attained;
* `tdet_transpose`  : invariance under transposition;
* `tdet_tmul_ge`    : **supermultiplicativity** `tdet A + tdet B ≤ tdet (A ⊗ B)`
  (the tropical Cauchy–Binet inequality); equality can fail — see
  `TropicalLA.Examples.tdet_tmul_strict` in `Examples.lean`;
* `tdet_diag_le` and `tdet_eq_trace_of_diagonally_dominant` : the diagonal always
  gives a lower bound, with equality under a Monge-type dominance condition.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











open TropicalLA in
theorem solution(A : Matrix ι ι ℝ) : tdet A.transpose = tdet A := by
  have key : ∀ (B : Matrix ι ι ℝ), tdet B.transpose ≤ tdet B := by
    intro B
    refine Finset.sup'_le _ _ fun σ _ => ?_
    have : permWeight B.transpose σ = permWeight B σ⁻¹ := by
      unfold permWeight
      rw [← Equiv.sum_comp σ (fun j => B j (σ⁻¹ j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.transpose_apply]
    rw [this]
    exact permWeight_le_tdet B σ⁻¹
  refine le_antisymm (key A) ?_
  simpa using key A.transpose
