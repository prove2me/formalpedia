-- Prove2me | solution 1 for lean_workbook_plus_18885
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:20.558113+00:00
-- url     : https://prove2.me/submissions/4f6bfe69-7d97-46a8-9a6d-cc87ecb1c44b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x = 0.5)
  (h₁ : y = -0.75) :
  y + x^2 = -0.5 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
