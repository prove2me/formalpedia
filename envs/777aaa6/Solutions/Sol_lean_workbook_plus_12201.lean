-- Prove2me | solution 1 for lean_workbook_plus_12201
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:46:58.187837+00:00
-- url     : https://prove2.me/submissions/53d6eca5-2604-4f4e-aa53-c68925165eb2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (t : ℝ) (h₀ : 2 ≤ t) : (t - 2) * (2 * t ^ 2 * (t - 2) + 5 * t * (t ^ 2 - 4) + t ^ 3 + t + 6) ≥ 0 := by
  have ht : 0 ≤ t := by linarith
  have ht2 : 0 ≤ t - 2 := by linarith
  have ht_sq : 0 ≤ t ^ 2 - 4 := by nlinarith [sq_nonneg (t - 2)]
  exact mul_nonneg ht2 (by positivity)
