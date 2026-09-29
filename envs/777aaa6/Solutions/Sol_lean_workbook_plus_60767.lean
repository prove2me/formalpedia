-- Prove2me | solution 1 for lean_workbook_plus_60767
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:55.701295+00:00
-- url     : https://prove2.me/submissions/f56eecfa-9260-4d6a-8e69-bfc957214f4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 3 * x ^ 2 + y ^ 2 - x * y ≥ (y - 1 / 2 * x) ^ 2 ∧ (y - 1 / 2 * x) ^ 2 ≥ 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
