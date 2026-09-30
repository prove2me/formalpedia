-- Prove2me | solution 1 for lean_workbook_plus_66666
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:28.624512+00:00
-- url     : https://prove2.me/submissions/a7361294-bc05-4580-a606-b46833bb530b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 + (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ≥
      (a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b) := by
  have hq : 0 < a * b + b * c + c * a := by positivity
  have hab : 0 < b + a := by positivity
  have hbc : 0 < c + b := by positivity
  have hac : 0 < a + c := by positivity
  have hid :
      2 + (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) -
          ((a + b) / (a + c) + (b + c) / (b + a) + (c + a) / (c + b)) =
        (a * (a * b - b * c) ^ 2 + b * (b * c - c * a) ^ 2 +
          c * (c * a - a * b) ^ 2) /
          ((a * b + b * c + c * a) * (b + a) * (c + b) * (a + c)) := by
    field_simp [ne_of_gt hq, ne_of_gt hab, ne_of_gt hbc, ne_of_gt hac] <;> ring
  have hn : 0 ≤ (a * (a * b - b * c) ^ 2 + b * (b * c - c * a) ^ 2 +
      c * (c * a - a * b) ^ 2) /
      ((a * b + b * c + c * a) * (b + a) * (c + b) * (a + c)) := by positivity
  linarith

#print axioms solution
