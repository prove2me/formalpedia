-- Prove2me | solution 1 for lean_workbook_plus_79646
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:06.401022+00:00
-- url     : https://prove2.me/submissions/a0191c4c-30ea-485c-8cca-60710f31d41b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ a b c : ℝ,
    a + b + c = 1 ∧ a * b + b * c + c * a = c^2 →
    (2 * c - 1)^2 / (6 * a^2 - 4 * a + 1) +
      (2 * b - 1)^2 / (6 * b^2 - 4 * b + 1) ≥
      4 * c^2 / (6 * (a^2 + b^2) - 4 * (a + b) + 2)) := by
  intro h
  have hbad := h (3 / 11) (2 / 11) (6 / 11) (by constructor <;> norm_num)
  norm_num at hbad

#print axioms solution
