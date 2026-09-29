-- Prove2me | solution 1 for lean_workbook_plus_31115
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:20.504354+00:00
-- url     : https://prove2.me/submissions/46dd74d6-3325-4fbb-a5e0-74e3f6c5b958

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : √(49 + 8 * Real.sqrt 3) = 1 + 4 * Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  nlinarith
