-- Prove2me | solution 1 for lean_workbook_plus_75036
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:28.116604+00:00
-- url     : https://prove2.me/submissions/e9557608-5aa4-4f1f-9b75-3157a759bd33

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem solution (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : x + y ≤ Real.sqrt 2 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 2)]
