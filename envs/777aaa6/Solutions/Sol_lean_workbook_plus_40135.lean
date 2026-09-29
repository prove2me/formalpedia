-- Prove2me | solution 1 for lean_workbook_plus_40135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:49.502507+00:00
-- url     : https://prove2.me/submissions/d2d77779-770d-4503-a3b5-26e56d0743c1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : (120:ℝ) / 49 > 4 / Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hn : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  apply (div_lt_iff₀ hn).2
  nlinarith
