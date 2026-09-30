-- Prove2me | solution 1 for lean_workbook_plus_63378
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:31.150277+00:00
-- url     : https://prove2.me/submissions/56b8f88b-9ccc-4ef1-ab86-4a192475ceda

import Mathlib
set_option autoImplicit false

theorem solution (t : ℝ) (ht : t > 0) : t ^ 3 ≥ 3 * t - 2   := by
  have h1 : (t - 1) ^ 2 * (t + 2) ≥ 0 := by positivity
  nlinarith [h1]

#print axioms solution
