-- Prove2me | solution 1 for lean_workbook_plus_51031
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:46.942369+00:00
-- url     : https://prove2.me/submissions/696d450e-7676-48d9-8137-588446663d64

import Mathlib
set_option autoImplicit false

theorem solution : 9 - 4 * Real.sqrt 5 = (2 - Real.sqrt 5) ^ 2   := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith only [h5]

#print axioms solution
