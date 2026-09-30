-- Prove2me | solution 1 for lean_workbook_plus_74923
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:09.070007+00:00
-- url     : https://prove2.me/submissions/6d430d18-164b-4a20-b341-256e8d7a6628

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ (a + b) * (b + c) * (c + a) := by
  have hid : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) -
      (a + b) * (b + c) * (c + a) =
      (a * b * c - 1) ^ 2 +
        ((a * b - a) ^ 2 + (a * b - b) ^ 2 + (b * c - b) ^ 2 +
          (b * c - c) ^ 2 + (c * a - c) ^ 2 + (c * a - a) ^ 2) / 2 := by ring
  have hn : 0 ≤ (a * b * c - 1) ^ 2 +
      ((a * b - a) ^ 2 + (a * b - b) ^ 2 + (b * c - b) ^ 2 +
        (b * c - c) ^ 2 + (c * a - c) ^ 2 + (c * a - a) ^ 2) / 2 := by positivity
  linarith

#print axioms solution
