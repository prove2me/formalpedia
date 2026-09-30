-- Prove2me | solution 1 for lean_workbook_plus_78550
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:02:06.992399+00:00
-- url     : https://prove2.me/submissions/b160dd83-12a7-4f69-b7aa-23b4d0c14374

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b : ℝ, 3 * a ^ 4 - 4 * a ^ 3 * b + b ^ 4 ≥ 0   := by
  simp only [ge_iff_le]
  refine' fun a b => _
  nlinarith [sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2)]

#print axioms solution
