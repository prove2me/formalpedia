-- Prove2me | solution 1 for lean_workbook_plus_69459
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:58:48.841488+00:00
-- url     : https://prove2.me/submissions/e5edd09a-c8b7-4630-aad1-75691a3203e1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (hbc : b = c) :
    a^4 + 9*a^2*b^2 + 4*b^4 ≥ 4*a^3*b + 10*a*b^3 := by
  have hpos : 0 ≤ (a-b)^2 + 3*b^2 := by
    nlinarith only [sq_nonneg (a-b), sq_nonneg b]
  have hprod := mul_nonneg (sq_nonneg (a-b)) hpos
  nlinarith only [hprod]
