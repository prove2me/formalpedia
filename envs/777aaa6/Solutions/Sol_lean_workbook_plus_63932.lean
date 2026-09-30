-- Prove2me | solution 1 for lean_workbook_plus_63932
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:36.600947+00:00
-- url     : https://prove2.me/submissions/c7a41e33-af73-440f-b2cf-a53d93112dbc

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) (ha : 1 < a) : 1 / (a - 1) + 1 / a + 1 / (a + 1) > 3 / a   := by
  have ha0 : 0 < a := by linarith
  have hm : 0 < a - 1 := by linarith
  have hp : 0 < a + 1 := by linarith
  have hd : 0 < a * (a - 1) * (a + 1) := by positivity
  apply (mul_lt_mul_iff_left₀ hd).mp
  field_simp [ne_of_gt ha0, ne_of_gt hm, ne_of_gt hp]
  nlinarith

#print axioms solution
