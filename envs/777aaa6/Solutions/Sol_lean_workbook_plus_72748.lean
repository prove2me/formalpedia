-- Prove2me | solution 1 for lean_workbook_plus_72748
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:02:10.837309+00:00
-- url     : https://prove2.me/submissions/598898ea-e70f-48a9-afa1-0aad46bbf74e

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) (h : x^5 - x^3 + x ≥ 3) : x^6 ≥ 5   := by
  have := sq_nonneg (x^2 - 1)
  nlinarith

#print axioms solution
