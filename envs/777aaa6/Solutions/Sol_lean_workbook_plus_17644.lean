-- Prove2me | solution 1 for lean_workbook_plus_17644
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:27.076632+00:00
-- url     : https://prove2.me/submissions/faf8e231-8de5-40bb-80bf-974b10855177

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≥ 0) : x^3 - 6 * x^2 + 8 * x + 4 > 0   := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x - 4)]

#print axioms solution
