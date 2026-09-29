-- Prove2me | solution 1 for lean_workbook_plus_25330
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:03:59.944493+00:00
-- url     : https://prove2.me/submissions/ee552c41-7fad-43a0-a844-1eae921f6378

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (n : ℕ) :
  (x^(n+1) + 1)^2 * (x + 1)^2 ≥ 4 * x * (x^(n+2) + 1) * (x^n + 1) := by
  rw [pow_add,pow_add]
  norm_num only [pow_one,pow_two]
  nlinarith only [sq_nonneg ((x-1)*(x*x^n-1))]
