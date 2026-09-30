-- Prove2me | solution 1 for lean_workbook_plus_78084
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:35:04.103847+00:00
-- url     : https://prove2.me/submissions/6abc3db3-f78a-4067-8a7c-a94af5f2f863

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution : ∀ x : ℝ, x^4 - 15 * x^3 + 76 * x^2 - 147 * x + 97 > 0 := by
  intro x
  nlinarith only [sq_nonneg (x^2 - (15 / 2 : ℝ) * x + 39 / 4),
    sq_nonneg (x - (3 / 2 : ℝ))]
