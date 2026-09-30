-- Prove2me | solution 1 for lean_workbook_plus_56763
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:51.460926+00:00
-- url     : https://prove2.me/submissions/451fc73c-7991-4c4a-aa14-d6e43cebc982

import Mathlib
set_option autoImplicit false

theorem solution : (5 + 2 * Real.sqrt 6)^3 + (5 - 2 * Real.sqrt 6)^3 = 970   := by
  simp [pow_three]
  ring_nf
  norm_num
  exact (by norm_num : (250 : ℝ) + 6 * 120 = 970)

#print axioms solution
