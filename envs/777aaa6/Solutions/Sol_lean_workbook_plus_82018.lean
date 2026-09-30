-- Prove2me | solution 1 for lean_workbook_plus_82018
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:15:20.667034+00:00
-- url     : https://prove2.me/submissions/4895e334-5f98-4791-a219-c6164b375d63

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution :
    ¬ (∀ x y z : ℝ,
      x ^ 3 * (x * y + x * z - y * z) * (y - z) ^ 2 +
        y ^ 3 * (x * y + y * z - z * x) * (z - x) ^ 2 +
        z ^ 3 * (z * x + y * z - x * y) * (x - y) ^ 2 ≥ 0) := by
  intro h
  have hbad := h (-1) (-2) (-3)
  ring_nf at hbad
  norm_num at hbad

#print axioms solution
