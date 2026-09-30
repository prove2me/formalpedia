-- Prove2me | solution 1 for lean_workbook_plus_69040
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:08.634546+00:00
-- url     : https://prove2.me/submissions/e72c1cb7-4846-491f-902a-09fa1bd981a3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : Int.floor (Real.sqrt 2021) = 44 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2021)
  have hn := Real.sqrt_nonneg 2021
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_ofNat]
  constructor <;> nlinarith

#print axioms solution
