-- Prove2me | solution 1 for lean_workbook_plus_78029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:37.723625+00:00
-- url     : https://prove2.me/submissions/f02ea978-ae38-448a-8a2b-210ddabf13b1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^2+y^2+z^2)*(1+1+1) ≥ (x+y+z)^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
