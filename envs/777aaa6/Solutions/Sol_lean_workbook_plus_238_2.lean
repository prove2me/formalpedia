-- Prove2me | solution 2 for lean_workbook_plus_238
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:31.482459+00:00
-- url     : https://prove2.me/submissions/7df29f09-2d1f-4a7e-b2ba-91dbd9de9e5f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x_1 x_2 : ℝ) (hx_1 : 0 < x_1) (hx_2 : 0 < x_2) : x_1 + x_2 ≥ 2 * Real.sqrt (x_1 * x_2) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x_1 * x_2 by positivity), Real.sqrt_nonneg (x_1 * x_2), sq_nonneg (x_1), sq_nonneg (x_2), sq_nonneg (x_1 - x_2), sq_nonneg (x_1 + x_2), mul_pos hx_1 hx_2])
