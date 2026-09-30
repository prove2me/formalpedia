-- Prove2me | solution 1 for lean_workbook_plus_61326
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:25.312309+00:00
-- url     : https://prove2.me/submissions/b2722a0e-dd7f-46ed-b369-65d6dd1da6ef

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a : ℝ) (ha : 0 ≤ a) :
    3*a^4 - 6*a^3 + 8*a^2 - 6*a + 3 ≥ 0 := by
  nlinarith [sq_nonneg (a^2 - a), sq_nonneg (a - 1), sq_nonneg a]
