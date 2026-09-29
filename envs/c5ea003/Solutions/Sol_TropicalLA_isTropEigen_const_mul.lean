-- Prove2me | solution 1 for TropicalLA.isTropEigen_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:52:40.016723+00:00
-- url     : https://prove2.me/submissions/ffb73f64-1682-4ad2-97f7-439f3877ed88

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue

open TropicalLA Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {A : Matrix ι ι ℝ} {lam c : ℝ} {v : ι → ℝ}

private lemma tmulVec_scale {c : ℝ} (hc : 0 ≤ c) (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
    tmulVec (fun i j => c * A i j) (fun i => c * v i) i = c * tmulVec A v i := by
  simp only [tmulVec]
  have h : ∀ j, c * A i j + c * v j = c * (A i j + v j) := fun j => by ring
  simp_rw [h]
  -- same as tropical sup scale
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => A i j + v j) hj) hc
  · obtain ⟨j0, hj0, hmax⟩ := exists_mem_eq_sup' (univ_nonempty (α := ι)) (fun j => A i j + v j)
    have : c * (A i j0 + v j0) ≤ univ.sup' univ_nonempty (fun j => c * (A i j + v j)) :=
      Finset.le_sup' (fun j => c * (A i j + v j)) hj0
    rwa [← hmax] at this

theorem solution (hc : 0 ≤ c) (h : IsTropEigen A lam v) :
    IsTropEigen (Matrix.of fun i j => c * A i j) (c * lam) (fun i => c * v i) := by
  intro i
  have hA : (Matrix.of fun i j => c * A i j : Matrix ι ι ℝ) = fun i j => c * A i j := by
    funext i j; simp [Matrix.of_apply]
  rw [hA, tmulVec_scale hc A v i, h i]
  ring
