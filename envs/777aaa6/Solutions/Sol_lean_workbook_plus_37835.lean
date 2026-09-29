-- Prove2me | solution 1 for lean_workbook_plus_37835
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:50.342507+00:00
-- url     : https://prove2.me/submissions/09d7aff4-7938-4359-ab6f-5dbdd641bec2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : 2 - Real.sqrt 2 > Real.sqrt 5 - 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  have hn5 := Real.sqrt_nonneg (5 : ℝ)
  have hb2 : Real.sqrt 2 < 3/2 := by nlinarith
  have hb5 : Real.sqrt 5 < 5/2 := by nlinarith
  linarith
