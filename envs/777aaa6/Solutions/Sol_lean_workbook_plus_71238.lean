-- Prove2me | solution 1 for lean_workbook_plus_71238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:15.653598+00:00
-- url     : https://prove2.me/submissions/0c3794b9-5170-427a-96e7-a70537bdcbe8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, 0 < x ∧ x < 1 → 2 * x ^ 8 - 2 * x ^ 3 + 3 * x ^ 6 - 3 * x + 6 > 3 * x ^ 3 + x := by
  intro x hx
  nlinarith only [sq_nonneg (x^3-5/6),sq_nonneg (x^4-1),sq_nonneg (x^2-1),sq_nonneg (x-1),sq_nonneg (x^4)]
