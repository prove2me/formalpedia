-- Prove2me | solution 1 for lean_workbook_plus_37830
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:04.36508+00:00
-- url     : https://prove2.me/submissions/b623db55-7d91-4812-bd41-43f6ef454631

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : |x - 4| < 1) : 1 / |x + 4| ≤ 1 / 7   := by
  rw [abs_sub_lt_iff] at hx
  rw [abs_eq_self.mpr (by linarith : 0 ≤ x + 4)]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

#print axioms solution
