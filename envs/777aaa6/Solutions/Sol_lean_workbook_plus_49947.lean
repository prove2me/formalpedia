-- Prove2me | solution 1 for lean_workbook_plus_49947
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:22.19048+00:00
-- url     : https://prove2.me/submissions/7011f55c-588a-4f34-abf6-25ba0303eb5e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 + 3 * (a * b + b * c + c * a) ≥ 4 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
