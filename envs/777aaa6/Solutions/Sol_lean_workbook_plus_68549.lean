-- Prove2me | solution 1 for lean_workbook_plus_68549
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:58:50.860563+00:00
-- url     : https://prove2.me/submissions/07a516f3-e217-4c07-a201-5f31682ff9c2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (habc : a*b*c > 0) :
    (a^2+b^2)*(a^4+b^2*c^2) ≥ a^2*b^2*(c+a)^2 := by
  nlinarith only [sq_nonneg (a^3-b^2*c)]
