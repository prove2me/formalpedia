-- Prove2me | solution 1 for lean_workbook_plus_43259
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:01.950024+00:00
-- url     : https://prove2.me/submissions/f3d3917f-c818-4247-89a1-25772ab87807

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x*y*z = 1) : x^2 + y^2 + z^2 ≥ x*y + y*z + x*z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
