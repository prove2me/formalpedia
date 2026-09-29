-- Prove2me | solution 1 for lean_workbook_plus_72328
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:41.793122+00:00
-- url     : https://prove2.me/submissions/f0c72200-e837-43d1-885f-a12bfe0f7586

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x + y ≥ 2 * Real.sqrt (x * y) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x * y by positivity), Real.sqrt_nonneg (x * y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
