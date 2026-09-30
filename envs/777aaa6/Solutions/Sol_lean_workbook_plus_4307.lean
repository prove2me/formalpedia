-- Prove2me | solution 1 for lean_workbook_plus_4307
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:26.155559+00:00
-- url     : https://prove2.me/submissions/f735cd6d-e72e-4a76-912f-146fd3222a94

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ a b c : ℝ, a * b * c > 0 →
    a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) := by
  intro h
  have hbad := h 1 (-2) (-3) (by norm_num)
  norm_num at hbad

#print axioms solution
