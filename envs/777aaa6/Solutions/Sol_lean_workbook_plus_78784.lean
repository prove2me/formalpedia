-- Prove2me | solution 1 for lean_workbook_plus_78784
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:03.410448+00:00
-- url     : https://prove2.me/submissions/f5108755-b089-4969-8360-75ac92559841

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y : ℝ, (8*x*y-(x+y)^2)^2-(x+y)^4 ≤ 0) := by
  intro h
  have h0 := h 1 (-1)
  norm_num at h0

#print axioms solution
