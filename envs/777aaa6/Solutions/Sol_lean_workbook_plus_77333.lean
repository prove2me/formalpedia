-- Prove2me | solution 1 for lean_workbook_plus_77333
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:34:01.60835+00:00
-- url     : https://prove2.me/submissions/a3fcb971-336e-4126-9870-a7d5c9c31546

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution : ∀ x y : ℝ, |x| / ((1 + x ^ 2) * (1 + y ^ 2)) ≤ 1 / 2 := by
  intro x y
  have hd : 0 < (1 + x^2) * (1 + y^2) := by positivity
  have hn : 0 ≤ (1 + x^2) * y^2 := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith only [sq_nonneg (|x| - 1), sq_abs x, hn]
