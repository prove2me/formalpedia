-- Prove2me | solution 1 for lean_workbook_plus_56752
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:50.498533+00:00
-- url     : https://prove2.me/submissions/94f8c473-65b9-4e2a-8ecf-889ef95b491e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : 3*x + 5*y = 29) (h₂ : 41*x + 23*y = 215) : x^2 + y^2 = 25 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
