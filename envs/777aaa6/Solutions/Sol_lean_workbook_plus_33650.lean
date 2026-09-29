-- Prove2me | solution 1 for lean_workbook_plus_33650
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:14.219398+00:00
-- url     : https://prove2.me/submissions/50c2716e-c0d6-41bc-82f8-ec030513fa10

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x + y = 10) :
  x * y ≤ 25 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
