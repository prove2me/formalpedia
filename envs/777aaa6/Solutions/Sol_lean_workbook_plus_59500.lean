-- Prove2me | solution 1 for lean_workbook_plus_59500
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:20.393978+00:00
-- url     : https://prove2.me/submissions/19f539c7-69a7-43e0-9d1f-bed88d25a672

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : x + y = 5 - z)
  (h₁ : x^2 + y^2 = 19 - z^2) :
  -1 ≤ z ∧ z ≤ 13/3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
