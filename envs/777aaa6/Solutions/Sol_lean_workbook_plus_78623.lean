-- Prove2me | solution 1 for lean_workbook_plus_78623
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:20.064652+00:00
-- url     : https://prove2.me/submissions/ae2825d7-26ad-496f-b01a-133459e6a0fd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) : Real.sqrt (a * b) * (2 - Real.sqrt (a * b)) ≤ 1 := by
  nlinarith [sq_nonneg (Real.sqrt (a * b) - 1)]

#print axioms solution
