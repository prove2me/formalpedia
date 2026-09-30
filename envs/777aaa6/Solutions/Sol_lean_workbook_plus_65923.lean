-- Prove2me | solution 1 for lean_workbook_plus_65923
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:55:02.314133+00:00
-- url     : https://prove2.me/submissions/a033297a-2a76-4b49-9963-f1e78649efd5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ⌊- Real.sqrt 17⌋ = -5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hn := Real.sqrt_nonneg 17
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_neg, Int.cast_ofNat]
  constructor <;> nlinarith

#print axioms solution
