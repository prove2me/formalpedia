-- Prove2me | solution 1 for lean_workbook_plus_81921
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:55:30.530169+00:00
-- url     : https://prove2.me/submissions/e7777f8c-8592-407a-a0b3-1af7aa70d32a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (hd : d ≥ 0) (hab : a + b + c + d = 4) :
    (a + b + c + d) ^ 2 ≥ 4 * (a * b + b * c + c * d + d * a) := by
  nlinarith only [sq_nonneg (a + c - b - d)]

#print axioms solution
