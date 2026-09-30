-- Prove2me | solution 1 for lean_workbook_plus_56597
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:42.660792+00:00
-- url     : https://prove2.me/submissions/6fe4e61d-3ef5-4a1e-be3a-be5d20fe2a0a

import Mathlib
set_option autoImplicit false

theorem solution : (Real.sqrt 3 + Real.sqrt 2)^6 + (Real.sqrt 3 - Real.sqrt 2)^6 = 970   := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    (Real.sqrt 3 + Real.sqrt 2) ^ 6 + (Real.sqrt 3 - Real.sqrt 2) ^ 6 =
        2 * ((Real.sqrt 3) ^ 2) ^ 3 +
        30 * ((Real.sqrt 3) ^ 2) ^ 2 * (Real.sqrt 2) ^ 2 +
        30 * (Real.sqrt 3) ^ 2 * ((Real.sqrt 2) ^ 2) ^ 2 +
        2 * ((Real.sqrt 2) ^ 2) ^ 3 := by ring
    _ = 970 := by rw [h3, h2]; norm_num

#print axioms solution
