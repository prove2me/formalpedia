-- Prove2me | solution 1 for lean_workbook_plus_34444
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:49.819589+00:00
-- url     : https://prove2.me/submissions/3beb260f-9ec4-4174-80b2-141bc4b9e6c0

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b : ℝ, 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 → Real.sqrt (a ^ 2 + b ^ 2) ≥ (a + b) / Real.sqrt 2   := by
  intro a b h
  apply Real.le_sqrt_of_sq_le
  have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, htwo]
  linarith

#print axioms solution
