-- Prove2me | solution 1 for lean_workbook_plus_74287
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T18:51:14.889713+00:00
-- url     : https://prove2.me/submissions/b5fbbf97-ae39-4d32-ac07-d85767e2a64c

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∃! x : ℝ, x ^ 2 = 2) := by
  rintro ⟨x, hx, hunique⟩
  have hneg : (-x) ^ 2 = 2 := by simpa only [neg_sq] using hx
  have hsame : -x = x := hunique (-x) hneg
  have hx0 : x = 0 := by linarith only [hsame]
  rw [hx0] at hx
  norm_num at hx

#print axioms solution
