-- Prove2me | solution 1 for lean_workbook_plus_49878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:22.667229+00:00
-- url     : https://prove2.me/submissions/b6e87ed2-e49c-4412-9987-f54d2f862ac5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (t : ℝ) : (t - 1) ^ 2 * (t ^ 2 + 2 * t + 5) ≥ 0 := by
  exact mul_nonneg (sq_nonneg (t-1)) (by nlinarith [sq_nonneg (t+1)])
