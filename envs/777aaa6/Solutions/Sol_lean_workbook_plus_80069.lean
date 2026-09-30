-- Prove2me | solution 1 for lean_workbook_plus_80069
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:12:59.272797+00:00
-- url     : https://prove2.me/submissions/933f9029-83d5-48ce-8877-ade5f1e58cba

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y : ℝ, x^3 + y^3 ≥ x*y*(x+y)) := by
  intro h
  have h0 := h (-1) 0
  norm_num at h0

#print axioms solution
