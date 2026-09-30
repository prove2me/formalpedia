-- Prove2me | solution 1 for lean_workbook_plus_65910
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:29.292404+00:00
-- url     : https://prove2.me/submissions/efc22609-114e-4142-b6e3-cae55590c740

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c d : ℝ) :
    (a+b+c+d)^2 ≥ 4*(a*b+b*c+c*d+d*a) := by
  nlinarith [sq_nonneg (a+c-b-d)]
