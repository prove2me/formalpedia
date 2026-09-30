-- Prove2me | solution 1 for lean_workbook_plus_76082
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:23:36.700766+00:00
-- url     : https://prove2.me/submissions/f95692e8-9b55-469a-9eb7-650832759604

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (a + b) + a / (1 + b) + b / (1 + a) ≥ 3 / 2 := by
  have hs : 0 < a + b := by positivity
  have ha1 : 0 < 1 + a := by positivity
  have hb1 : 0 < 1 + b := by positivity
  have hs2 : 0 < a + b + 2 := by positivity
  have hid : 1 / (a + b) + a / (1 + b) + b / (1 + a) - 3 / 2 =
      (a + b - 2) ^ 2 / (2 * (a + b) * (a + b + 2)) +
        (a + b + 1) * (a - b) ^ 2 / ((1 + a) * (1 + b) * (a + b + 2)) := by
    field_simp [ne_of_gt hs, ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hs2] <;> ring
  have hn : 0 ≤ (a + b - 2) ^ 2 / (2 * (a + b) * (a + b + 2)) +
      (a + b + 1) * (a - b) ^ 2 / ((1 + a) * (1 + b) * (a + b + 2)) := by positivity
  linarith

#print axioms solution
