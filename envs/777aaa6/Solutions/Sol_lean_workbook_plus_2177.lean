-- Prove2me | solution 1 for lean_workbook_plus_2177
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:22.207807+00:00
-- url     : https://prove2.me/submissions/477809db-813b-4b97-bf0e-6180a851d2a1

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.sqrt ((1 + a) * (1 + b)) ≥ 1 + Real.sqrt (a * b)   := by
  have hs : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hm : Real.sqrt (a * b) ≤ (a + b) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (a - b)]
  apply Real.le_sqrt_of_sq_le
  nlinarith only [hs, hm]

#print axioms solution
