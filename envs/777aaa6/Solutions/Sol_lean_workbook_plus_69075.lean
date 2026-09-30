-- Prove2me | solution 1 for lean_workbook_plus_69075
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:38.394789+00:00
-- url     : https://prove2.me/submissions/c99d1aa6-58ad-4656-8b8e-79f6b429bbee

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) :
    2 * (a ^ 2 - a * b + b ^ 2) * (c ^ 2 - c * d + d ^ 2) ≥
      a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := by
  nlinarith only [sq_nonneg ((a - b) * (c - d)), sq_nonneg (a * d - b * c)]

#print axioms solution
