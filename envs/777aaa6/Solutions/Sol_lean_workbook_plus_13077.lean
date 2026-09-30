-- Prove2me | solution 1 for lean_workbook_plus_13077
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:46:48.560703+00:00
-- url     : https://prove2.me/submissions/e4a94c1c-c203-4365-a3e5-b3758174a787

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : abs x < 1) : ∑' n : ℕ, x ^ n = 1 / (1 - x)   := by
  simpa only [one_div] using (tsum_geometric_of_abs_lt_one hx)

#print axioms solution
