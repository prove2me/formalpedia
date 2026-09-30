-- Prove2me | solution 1 for lean_workbook_plus_33967
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:58.348549+00:00
-- url     : https://prove2.me/submissions/875a79e7-0cfb-43a3-af3d-0bc3246da236

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : |(a + b) / 2| ≤ (|a| + |b|) / 2   := by
  rw [abs_div]
  norm_num
  linarith [abs_add_le a b]

#print axioms solution
