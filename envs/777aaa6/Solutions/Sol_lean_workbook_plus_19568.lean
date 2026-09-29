-- Prove2me | solution 1 for lean_workbook_plus_19568
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:42.201042+00:00
-- url     : https://prove2.me/submissions/8b912f18-5635-4519-a1ed-9959374cdf44

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (ha : 0 < a) : 1 / Real.sqrt a > 2 * (Real.sqrt (a + 1) - Real.sqrt a) := by
  have hs0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  have ht := Real.sq_sqrt (show 0 ≤ a+1 by linarith)
  have hd : 0 < Real.sqrt (a+1)-Real.sqrt a := sub_pos.mpr (Real.sqrt_lt_sqrt ha.le (by linarith))
  have hp := sq_pos_of_pos hd
  apply (lt_div_iff₀ hs0).2
  nlinarith
