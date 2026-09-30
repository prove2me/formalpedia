-- Prove2me | solution 1 for lean_workbook_plus_61117
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:58:58.011252+00:00
-- url     : https://prove2.me/submissions/0ea966f5-f7d2-4dec-a3e3-cb962f3e59ff

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) (h : a ≤ 2) : Real.sqrt ((a - 2) ^ 2) = 2 - a   := by
  simp [Real.sqrt_sq_eq_abs, abs_of_nonpos (sub_nonpos.2 h)]

#print axioms solution
