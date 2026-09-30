-- Prove2me | solution 1 for lean_workbook_plus_37661
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:06:43.60909+00:00
-- url     : https://prove2.me/submissions/9044cb5f-b2b9-429e-83dc-53061003c766

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

theorem quartic_variance_remainder (a b c : ℝ) :
    (5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a)) ^ 2 -
      (15 * (a ^ 4 + b ^ 4 + c ^ 4) + 12 * a * b * c * (a + b + c)) =
    5 * ((a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4) +
      12 * ((c * (a - b)) ^ 2 + (a * (b - c)) ^ 2 + (b * (c - a)) ^ 2) := by
  ring

theorem solution (a b c : ℝ) :
    (5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a)) ^ 2 ≥
      15 * (a ^ 4 + b ^ 4 + c ^ 4) + 12 * a * b * c * (a + b + c) := by
  have h : 0 ≤ 5 * ((a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4) +
      12 * ((c * (a - b)) ^ 2 + (a * (b - c)) ^ 2 + (b * (c - a)) ^ 2) := by
    positivity
  linarith [quartic_variance_remainder a b c]

#print axioms solution
