-- Prove2me | solution 1 for lean_workbook_plus_71362
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:02.345468+00:00
-- url     : https://prove2.me/submissions/50bbca61-f300-4abb-b618-81c2fee2c230

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ x : ℝ, x ≤ (Real.sqrt 5 - 1) / 2 ∧ x ≤ 0 →
    x ^ 3 * (1 + Real.sqrt (3 - x ^ 2)) + x ^ 2 ≤ 1 := by
  intro x hx
  have hc : x ^ 3 ≤ 0 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hx.2]
  have ht := mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg (3 - x ^ 2))
  have hp := mul_nonneg (sq_nonneg (x + 2 / 3))
    (show 0 ≤ (1 : ℝ) / 3 - x by linarith [hx.2])
  nlinarith

#print axioms solution
