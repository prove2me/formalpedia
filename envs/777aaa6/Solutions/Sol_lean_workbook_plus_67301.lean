-- Prove2me | solution 1 for lean_workbook_plus_67301
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:19.273538+00:00
-- url     : https://prove2.me/submissions/318535e5-6293-42b7-abbe-4fe80870b4ea

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 + y^3 ≥ x * y^2 + x^2 * y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
