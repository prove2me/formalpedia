-- Prove2me | solution 1 for lean_workbook_plus_11863
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:53.325445+00:00
-- url     : https://prove2.me/submissions/e53456b6-10d0-4833-aad3-48686320815b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y) * (y + z) * (z + x) = (x + y + z) * (x*y + y*z + z*x) - x*y*z := by
  (intros; linarith)
