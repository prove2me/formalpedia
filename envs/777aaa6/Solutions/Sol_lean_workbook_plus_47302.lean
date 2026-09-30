-- Prove2me | solution 1 for lean_workbook_plus_47302
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:38.684714+00:00
-- url     : https://prove2.me/submissions/fa832b4e-f9ff-4efe-aa3a-3a60e1511940

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : |a| - |b| ≤ |a + b| ∧ |a + b| ≤ |a| + |b|   := by
  constructor
  · have h : |a| ≤ |a + b| + |b| := by simpa using abs_add_le (a + b) (-b)
    linarith
  · exact abs_add_le a b

#print axioms solution
