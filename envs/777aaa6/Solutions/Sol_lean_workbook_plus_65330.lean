-- Prove2me | solution 1 for lean_workbook_plus_65330
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:30.709075+00:00
-- url     : https://prove2.me/submissions/23af610c-260a-4f53-9b40-4ca1ccc24405

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a - b) * (b - c) * (c - d) * (d - a) + (a - c) ^ 2 * (b - d) ^ 2 ≥ 0 := by
  nlinarith only [sq_nonneg ((a - b) * (c - d) + (a - c) * (b - d)),
    sq_nonneg ((a - d) * (b - c))]

#print axioms solution
