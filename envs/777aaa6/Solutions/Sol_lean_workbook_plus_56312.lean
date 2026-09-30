-- Prove2me | solution 1 for lean_workbook_plus_56312
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:49.896591+00:00
-- url     : https://prove2.me/submissions/fcaaaea0-989a-43c2-bd7a-1196abfd8288

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : (a^4 + 1) * (b^4 + 1) ≥ (a^2 + b^2)^2   := by
  simp [sq]
  nlinarith [sq_nonneg (a^2 * b^2 - 1)]

#print axioms solution
