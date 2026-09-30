-- Prove2me | solution 1 for lean_workbook_plus_74437
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:39:20.933376+00:00
-- url     : https://prove2.me/submissions/5d6249d5-e769-4775-b5ff-f645474e8522

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a : ℝ) : a^6 + 2*a^5 + a^4 + 4*a^3 + 7*a^2 + 18*a + 55 > 0 := by
  nlinarith [sq_nonneg (a^3+a^2+2), sq_nonneg (a+3)]
