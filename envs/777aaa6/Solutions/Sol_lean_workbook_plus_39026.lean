-- Prove2me | solution 1 for lean_workbook_plus_39026
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:12.007291+00:00
-- url     : https://prove2.me/submissions/faa07ede-ae10-4d4a-a695-4ec5b7136b2f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (3 * a + b) + 1 / (a + 3 * b) ≤ (1 / 4) * (1 / a + 1 / b) := by
  have hd1 : 0 < 3 * a + b := by positivity
  have hd2 : 0 < a + 3 * b := by positivity
  have hid : (1 / 4) * (1 / a + 1 / b) -
      (1 / (3 * a + b) + 1 / (a + 3 * b)) =
      3 * (a + b) * (a - b)^2 / (4 * a * b * (3 * a + b) * (a + 3 * b)) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hd1, ne_of_gt hd2]
    <;> ring
  have hn : 0 ≤ (1 / 4) * (1 / a + 1 / b) -
      (1 / (3 * a + b) + 1 / (a + 3 * b)) := by
    rw [hid]
    positivity
  linarith
