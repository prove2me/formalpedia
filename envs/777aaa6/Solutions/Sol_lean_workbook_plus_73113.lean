-- Prove2me | solution 1 for lean_workbook_plus_73113
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:19.316732+00:00
-- url     : https://prove2.me/submissions/7be6872b-552e-415b-abff-8315be22c083

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem quartic_bound (a b : ℝ) :
    a * b * (a^2 + b^2) ≤ (a+b)^4 / 8 := by
  nlinarith only [sq_nonneg ((a-b)^2)]

theorem solution : ∀ a b c : ℝ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 →
    a * b * (a ^ 2 + b ^ 2) ≤ (a + b) ^ 4 / 8 := by
  intro a b c _
  exact quartic_bound a b
