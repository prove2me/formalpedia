-- Prove2me | solution 1 for lean_workbook_plus_57874
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:42.40806+00:00
-- url     : https://prove2.me/submissions/79eadf1f-e439-478a-a360-3d8423511a27

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x^2 + x * y + x = 1)
  (h₁ : y^2 + x * y + x + y = 1)
  (h₂ : 0 < x ∧ 0 < y) :
  x^3 - 2 * x^2 - x + 1 = 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
