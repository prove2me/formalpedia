-- Prove2me | solution 1 for lean_workbook_plus_72198
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:28.104136+00:00
-- url     : https://prove2.me/submissions/c8d9a04c-6989-482c-9e37-6e72a01751e7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) ≥
      2 * (a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b) := by
  nlinarith only [sq_nonneg ((a - b) ^ 2), sq_nonneg ((b - c) ^ 2),
    sq_nonneg ((c - a) ^ 2)]

#print axioms solution
