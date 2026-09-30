-- Prove2me | solution 1 for lean_workbook_plus_71714
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:00.042746+00:00
-- url     : https://prove2.me/submissions/cd7b8c07-81a1-4274-a2e3-05f9fc6406fc

import Mathlib

theorem solution : ¬ (∀ x y z : ℝ,
    (1 + x + y) ^ 2 + (1 + y + z) ^ 2 + (1 + z + x) ^ 2 ≤
      3 * (x + y + z) ^ 2) := by
  intro h
  have hz := h 0 0 0
  norm_num at hz

#print axioms solution
