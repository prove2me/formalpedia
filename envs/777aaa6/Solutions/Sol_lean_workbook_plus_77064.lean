-- Prove2me | solution 1 for lean_workbook_plus_77064
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:50.603292+00:00
-- url     : https://prove2.me/submissions/7a6fa6b9-f12f-4a15-b06b-412b70905ea9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 - y^2 < 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
