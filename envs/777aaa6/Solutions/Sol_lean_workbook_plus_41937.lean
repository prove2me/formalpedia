-- Prove2me | solution 1 for lean_workbook_plus_41937
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:48.535029+00:00
-- url     : https://prove2.me/submissions/ea2dfa2d-bb64-435f-bd53-1ae67328ddf5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x*y + y*z + z*x)^2 ≥ 3*(x + y + z)*x*y*z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
