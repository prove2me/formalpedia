-- Prove2me | solution 1 for lean_workbook_plus_77811
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:20.911793+00:00
-- url     : https://prove2.me/submissions/0cf6196e-b344-4d95-b88c-e52bf5b84a25

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ x y z : ℝ,
    (3 * x * y * z + x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ^ 2 ≥
      4 * x * y * z * (x * y + y * z + z * x) * (x + y + z)) := by
  intro h
  have hbad := h (-2) (-1) 1
  norm_num at hbad

#print axioms solution
