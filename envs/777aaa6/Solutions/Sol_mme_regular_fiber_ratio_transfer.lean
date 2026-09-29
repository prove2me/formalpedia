-- Prove2me | solution 1 for mme_regular_fiber_ratio_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:52:39.50032+00:00
-- url     : https://prove2.me/submissions/86e5002f-355a-4497-b3e3-79044b93e6ea

import Mathlib

set_option autoImplicit false
set_option warningAsError true

/-- If two finite families are regular over the same nonempty vertex set,
then a total-cardinality ratio transfers without loss to their common fiber
degrees. -/
theorem solution
    {Edge : Type} [DecidableEq Edge]
    (ambient target : Finset Edge)
    (wordCount ambientDegree targetDegree : ℕ) (rho : ℝ)
    (hword : 0 < wordCount)
    (hambient : ambient.card = wordCount * ambientDegree)
    (htarget : target.card = wordCount * targetDegree)
    (hratio : (ambient.card : ℝ) ≤ rho * (target.card : ℝ)) :
    (ambientDegree : ℝ) ≤ rho * (targetDegree : ℝ) := by
  have hwordR : (0 : ℝ) < wordCount := by exact_mod_cast hword
  have hscaled :
      (wordCount : ℝ) * (ambientDegree : ℝ) ≤
        (wordCount : ℝ) * (rho * (targetDegree : ℝ)) := by
    calc
      (wordCount : ℝ) * (ambientDegree : ℝ) =
          (ambient.card : ℝ) := by
        exact_mod_cast hambient.symm
      _ ≤ rho * (target.card : ℝ) := hratio
      _ = (wordCount : ℝ) *
          (rho * (targetDegree : ℝ)) := by
        rw [htarget]
        push_cast
        ring
  exact (mul_le_mul_iff_of_pos_left hwordR).mp hscaled
