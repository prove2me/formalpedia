-- Prove2me | solution 1 for lean_workbook_plus_74575
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:11:38.291951+00:00
-- url     : https://prove2.me/submissions/1a33de4e-826c-458b-a275-972756b3c94c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    (a + (b + c) / 4) *
      (a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b)) =
    b * c * (b - c) ^ 2 + (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 +
      (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4 := by
  ring
