-- Prove2me | solution 1 for TropicalLA.tdet_tmul_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:58.866001+00:00
-- url     : https://prove2.me/submissions/60858431-c8f9-4340-9aeb-1467f3b77539

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_exists_permWeight_eq_tdet
import Theorems.Thm_TropicalLA_le_tmul
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
theorem solution[Nonempty ι] (A B : Matrix ι ι ℝ) : tdet A + tdet B ≤ tdet (tmul A B) := by
  obtain ⟨σ, hσ⟩ := exists_permWeight_eq_tdet A
  obtain ⟨τ, hτ⟩ := exists_permWeight_eq_tdet B
  have hB : permWeight B τ = ∑ i, B (σ i) (τ (σ i)) := by
    unfold permWeight
    rw [← Equiv.sum_comp σ (fun j => B j (τ j))]
  have hkey : permWeight A σ + permWeight B τ ≤ permWeight (tmul A B) (σ.trans τ) := by
    rw [hB]
    simp only [permWeight, Equiv.trans_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => le_tmul A B i (τ (σ i)) (σ i)
  rw [hσ, hτ]
  exact le_trans hkey (permWeight_le_tdet _ _)
