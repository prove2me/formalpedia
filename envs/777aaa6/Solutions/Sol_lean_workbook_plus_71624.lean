-- Prove2me | solution 1 for lean_workbook_plus_71624
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:17.91914+00:00
-- url     : https://prove2.me/submissions/7455aa96-a44f-45f0-94cc-1e3a8d71a921

import Mathlib
set_option autoImplicit false

theorem solution : ∃ x y z : ℝ,
    (y + 1) / 3 = -(x + 1) * (x - 1) ^ 2 ∧
    (z + 1) / 4 = -(y + 1) * (y - 1) ^ 2 ∧
    (x + 1) / 5 = -(z + 1) * (z - 1) ^ 2 := by
  refine ⟨-1, -1, -1, ?_⟩
  norm_num

#print axioms solution
