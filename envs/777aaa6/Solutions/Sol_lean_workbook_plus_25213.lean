-- Prove2me | solution 1 for lean_workbook_plus_25213
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:48.276354+00:00
-- url     : https://prove2.me/submissions/58df96de-089b-4550-b7ce-4f53ae4ae882

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) (h : a > 1) : 1 / (a - 1) + 1 / a + 1 / (a + 1) > 3 / a   := by
  have ha0 : 0 < a := by linarith
  have ham : 0 < a - 1 := by linarith
  have hap : 0 < a + 1 := by linarith
  have he : 1 / (a - 1) + 1 / a + 1 / (a + 1) - 3 / a =
      2 / (a * (a - 1) * (a + 1)) := by
    field_simp [ne_of_gt ha0, ne_of_gt ham, ne_of_gt hap]
    <;> ring
  have hp : 0 < 2 / (a * (a - 1) * (a + 1)) := by positivity
  linarith

#print axioms solution
