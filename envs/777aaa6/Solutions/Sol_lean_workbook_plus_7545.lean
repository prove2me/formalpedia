-- Prove2me | solution 1 for lean_workbook_plus_7545
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:58.705714+00:00
-- url     : https://prove2.me/submissions/2d98c4ff-c96e-4633-9dbb-d723c838c29c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * a * (a + b) * (a + b) + b * b * (b + c) * (b + c) + c * c * (c + a) * (c + a) + 1 / 2 * (a * a - b * b) * (a * a - b * b) + 1 / 2 * (b * b - c * c) * (b * b - c * c) + 1 / 2 * (c * c - a * a) * (c * c - a * a) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
