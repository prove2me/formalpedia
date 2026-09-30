-- Prove2me | solution 1 for lean_workbook_plus_72704
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:22:31.745639+00:00
-- url     : https://prove2.me/submissions/8f7c7fc3-7c4f-432c-8b65-45fb781a7187

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem quartic_uniform_positive_bound (x : ℝ) :
    (2 : ℝ) / 3 ≤ x ^ 4 + x ^ 3 - x + 1 := by
  have h : 36 * (x ^ 4 + x ^ 3 - x + 1) =
      9 * (2 * x ^ 2 + x - 1) ^ 2 + 3 * (3 * x - 1) ^ 2 + 24 := by ring
  nlinarith only [h, sq_nonneg (2 * x ^ 2 + x - 1), sq_nonneg (3 * x - 1)]

theorem solution : ¬ ∃ x : ℝ, x ^ 4 + x ^ 3 - x + 1 = 0 := by
  rintro ⟨x, hx⟩
  have := quartic_uniform_positive_bound x
  linarith

#print axioms solution
#print axioms quartic_uniform_positive_bound
