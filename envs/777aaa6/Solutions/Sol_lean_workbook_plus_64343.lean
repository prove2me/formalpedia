-- Prove2me | solution 1 for lean_workbook_plus_64343
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:48.964914+00:00
-- url     : https://prove2.me/submissions/88746613-45cc-4d26-9017-7ce1a96ec1ca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x*y*z = 1) : 2*(x + y + z - 3)^2 + x^2 + y^2 + z^2 - x*y - y*z - z*x ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
