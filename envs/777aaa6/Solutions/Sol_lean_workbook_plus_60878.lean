-- Prove2me | solution 1 for lean_workbook_plus_60878
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:34.562802+00:00
-- url     : https://prove2.me/submissions/7f1f1a00-ebf8-45b2-a3f7-8f8e11c8e5b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x + y = 4) (h₂ : x * y = -12) : x^2 + 5 * (x * y) + y^2 = -20 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
