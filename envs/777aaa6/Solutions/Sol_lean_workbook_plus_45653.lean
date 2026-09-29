-- Prove2me | solution 1 for lean_workbook_plus_45653
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:24.932599+00:00
-- url     : https://prove2.me/submissions/416b2e4b-c731-4962-b36f-03aa7b16ce51

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : (1 + Real.sqrt 12) > Real.sqrt 6 := by
  have h := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 6 by norm_num) (show (6:ℝ)<12 by norm_num)
  linarith
