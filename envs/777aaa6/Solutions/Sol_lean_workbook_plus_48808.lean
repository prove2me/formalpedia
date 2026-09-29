-- Prove2me | solution 1 for lean_workbook_plus_48808
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:19.104633+00:00
-- url     : https://prove2.me/submissions/b444ec76-02fc-4261-9c6c-5d87d024b39a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : √(4 + 2 * Real.sqrt 3) = 1 + Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  nlinarith
