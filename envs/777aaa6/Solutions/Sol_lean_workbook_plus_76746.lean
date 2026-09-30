-- Prove2me | solution 1 for lean_workbook_plus_76746
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:59.073495+00:00
-- url     : https://prove2.me/submissions/3fbc10c6-8682-4e5c-84b6-f7d0ccd9f12f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution : ∀ x : ℝ,
    3 * (x - 1) ^ 2 * (2 * x ^ 4 + 4 * x ^ 3 + 21 * x ^ 2 + 10 * x + 44) ≥ 0 := by
  intro x
  apply mul_nonneg (show 0 ≤ 3 * (x - 1) ^ 2 by positivity)
  nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x + 1), sq_nonneg x]
