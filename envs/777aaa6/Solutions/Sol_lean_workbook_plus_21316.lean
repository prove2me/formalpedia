-- Prove2me | solution 1 for lean_workbook_plus_21316
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:35.0467+00:00
-- url     : https://prove2.me/submissions/91f2e485-7e23-41a8-9e44-a1380684403c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ⌊Real.sqrt 1700⌋ = 41 := by
  apply Int.floor_eq_iff.mpr
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 1700 by norm_num)
  have hn := Real.sqrt_nonneg (1700:ℝ)
  constructor <;> norm_num <;> nlinarith
