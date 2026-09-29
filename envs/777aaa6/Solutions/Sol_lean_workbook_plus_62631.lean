-- Prove2me | solution 1 for lean_workbook_plus_62631
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:23.105394+00:00
-- url     : https://prove2.me/submissions/d711db31-aac9-4472-a950-0921d014291e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (1^2 + 1^2 + 1^2) * ((x + y)^2 + (y + z)^2 + (z + x)^2) ≥ ((x + y) + (y + z) + (x + z))^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
