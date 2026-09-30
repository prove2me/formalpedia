-- Prove2me | solution 1 for lean_workbook_plus_53026
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:04.852214+00:00
-- url     : https://prove2.me/submissions/1b08d3e7-6f03-47be-896b-4c7639ecfdb0

import Mathlib.Analysis.Complex.Basic

theorem solution (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : Real.sqrt ((1 + α) * (1 + β)) ≥ 1 + Real.sqrt (α * β) := by
  have hab : 0 ≤ α * β := by positivity
  have hs : Real.sqrt (α * β) ^ 2 = α * β := Real.sq_sqrt hab
  have hs0 : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
  rw [ge_iff_le]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (Real.sqrt α - Real.sqrt β), Real.sq_sqrt hα.le, Real.sq_sqrt hβ.le,
    Real.sqrt_mul hα.le β, sq_nonneg (Real.sqrt (α * β) - 1)]
