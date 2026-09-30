-- Prove2me | solution 1 for lean_workbook_plus_47980
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:21.088246+00:00
-- url     : https://prove2.me/submissions/e789612e-884e-46b2-8f3b-550fbed306a3

import Mathlib
set_option autoImplicit false

theorem solution (z w : ℂ) : ‖z - w‖ ≥ ‖‖z‖ - ‖w‖‖   := by
  simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le z w

#print axioms solution
