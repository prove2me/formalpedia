-- Prove2me | solution 1 for lean_workbook_plus_75244
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:36:35.158753+00:00
-- url     : https://prove2.me/submissions/b6fb5b51-c15a-4607-bbf5-7884ec6a1da5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y : ℝ) :
    (x^2*y^2)/4 + x^2 + y^2 + x^2*y + x*y^2 + (5/2)*x*y + x + y + 1/4 ≥ 0 := by
  nlinarith [sq_nonneg (x*y/2+x+y+1/2)]
