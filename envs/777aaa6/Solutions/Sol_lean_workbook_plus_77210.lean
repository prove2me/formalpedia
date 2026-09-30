-- Prove2me | solution 1 for lean_workbook_plus_77210
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:45.296638+00:00
-- url     : https://prove2.me/submissions/8de47923-71b6-4356-9d34-418187fdaf1f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : 1 + Real.sqrt 6 = Real.sqrt (1 + 6 + 2 * Real.sqrt 6) := by
  symm
  apply Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity) |>.mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

#print axioms solution
