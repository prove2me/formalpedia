-- Prove2me | solution 1 for lean_workbook_plus_21669
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:37.750122+00:00
-- url     : https://prove2.me/submissions/a02beeb5-f666-4f82-9728-ce4cdaeacf81

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : (140 : ℝ) / 99 < Real.sqrt 2 ∧ Real.sqrt 2 < 99 / 70 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith
