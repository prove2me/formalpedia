-- Prove2me | solution 1 for lean_workbook_plus_69297
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:17.768411+00:00
-- url     : https://prove2.me/submissions/421366d4-b3e8-499f-b079-1d16ae29394f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≥
      2 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 7 := by
  have hq : 0 < a * b + b * c + a * c := by positivity
  have hid :
      (a + b + c) * (1 / a + 1 / b + 1 / c) -
          (2 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 7) =
        ((a + b + c) * ((a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 +
          (c * a - a * b) ^ 2) + a * b * c *
            ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2)) /
          (2 * a * b * c * (a * b + b * c + a * c)) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hq] <;> ring
  have hn : 0 ≤ ((a + b + c) * ((a * b - b * c) ^ 2 +
      (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2) + a * b * c *
      ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2)) /
      (2 * a * b * c * (a * b + b * c + a * c)) := by positivity
  linarith

#print axioms solution
