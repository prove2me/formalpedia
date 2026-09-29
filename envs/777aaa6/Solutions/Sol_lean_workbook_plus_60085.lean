-- Prove2me | solution 1 for lean_workbook_plus_60085
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:16.136777+00:00
-- url     : https://prove2.me/submissions/ac3888a1-b7f2-4b15-887a-4b523356da1b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : y > 1) (h' : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
