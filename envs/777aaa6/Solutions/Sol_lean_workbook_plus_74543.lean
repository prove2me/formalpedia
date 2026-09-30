-- Prove2me | solution 1 for lean_workbook_plus_74543
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:50.705655+00:00
-- url     : https://prove2.me/submissions/fe180f3d-523b-4ee1-a6f1-f62fbf78f1a3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a - b) * (2 * a + b) * (a ^ 2 + b ^ 2) +
      (b - c) * (2 * b + c) * (b ^ 2 + c ^ 2) +
      (c - a) * (2 * c + a) * (c ^ 2 + a ^ 2) ≥ 0 := by
  nlinarith only [sq_nonneg ((a - b) * (a + b - c)),
    sq_nonneg ((b - c) * (b + c - a)), sq_nonneg ((c - a) * (c + a - b)),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]

#print axioms solution
