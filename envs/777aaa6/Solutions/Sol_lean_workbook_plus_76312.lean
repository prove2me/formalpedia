-- Prove2me | solution 1 for lean_workbook_plus_76312
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:53:48.070711+00:00
-- url     : https://prove2.me/submissions/01d1648e-c351-4815-8958-2e4572d7e3ad

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ⌊Real.sqrt 850⌋ = 29 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 850)
  have hn := Real.sqrt_nonneg 850
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_ofNat]
  constructor <;> nlinarith

#print axioms solution
