-- Prove2me | solution 1 for lean_workbook_plus_77315
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:12.197502+00:00
-- url     : https://prove2.me/submissions/7e9b4f5c-4687-458a-9865-d325f91ec3b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 1) (h₂ : x^2 + y^2 + z^2 = 2) (h₃ : x^3 + y^3 + z^3 = 3) : x*y + y*z + z*x = -1/2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
