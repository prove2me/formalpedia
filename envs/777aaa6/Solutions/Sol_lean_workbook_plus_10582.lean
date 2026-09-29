-- Prove2me | solution 1 for lean_workbook_plus_10582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:20:00.511039+00:00
-- url     : https://prove2.me/submissions/0b689cea-087e-4aa1-9213-650dfeb86358

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : (x + y) * (x - y) ^ 2 + 2 * (x - 1) * (y - 1) ≥ 0 := by
  by_cases hs : 1 ≤ x+y
  · have hp : 0 ≤ 2*(x+y)-1 := by linarith
    nlinarith [mul_nonneg hp (sq_nonneg (x-y)), sq_nonneg (x+y-2)]
  · have hx1 : 0 ≤ 1-x := by linarith
    have hy1 : 0 ≤ 1-y := by linarith
    nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x-y)), mul_nonneg hx1 hy1]
