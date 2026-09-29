-- Prove2me | solution 1 for lean_workbook_plus_41710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:31:35.460603+00:00
-- url     : https://prove2.me/submissions/7bc9c938-b735-41e0-8aa0-25236859506b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : x ≥ Real.sqrt 3) : Real.sqrt (x ^ 2 - 3) ≤ 2 * x - 3 := by
  have hs0 := Real.sqrt_nonneg (3:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hr : 0 ≤ 2*x-3 := by nlinarith only [hx, hs0, hs2]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact hr
  · nlinarith only [sq_nonneg (x-2)]
