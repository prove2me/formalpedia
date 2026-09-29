-- Prove2me | solution 1 for lean_workbook_plus_44961
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:26.654805+00:00
-- url     : https://prove2.me/submissions/8c6a7c3f-e2d3-4ae8-8198-8ce7d88a1d31

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x ^ 2 + y ^ 2) / 2 ≥ (x + y) ^ 2 / 4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
