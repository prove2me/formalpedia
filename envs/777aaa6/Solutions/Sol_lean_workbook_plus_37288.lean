-- Prove2me | solution 1 for lean_workbook_plus_37288
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:12.100774+00:00
-- url     : https://prove2.me/submissions/3489ed49-a8e6-4fb0-ad00-51fe8e1efb4e

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx: 1 ≤ x) : x^3 - 5 * x^2 + 8 * x - 4 ≥ 0   := by
  have h : 0 ≤ (x - 1) * (x - 2) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (x - 2))
  nlinarith

#print axioms solution
