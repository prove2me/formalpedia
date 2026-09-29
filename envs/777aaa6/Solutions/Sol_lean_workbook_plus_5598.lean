-- Prove2me | solution 1 for lean_workbook_plus_5598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:21.967719+00:00
-- url     : https://prove2.me/submissions/86f630e9-554f-4c78-8015-627018155f29

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) * (x - y) ^ 2 + 2 * (x - 1) * (y - 1) ≥ 0 := by
  by_cases hs : 1/2 ≤ x+y
  · have hp := mul_nonneg (show 0≤x+y-1/2 by linarith) (sq_nonneg (x-y))
    nlinarith only [hp,sq_nonneg (x+y-2)]
  · have hp := mul_nonneg_of_nonpos_of_nonpos (show x-1≤0 by linarith) (show y-1≤0 by linarith)
    have hq := mul_nonneg (add_nonneg hx hy) (sq_nonneg (x-y))
    nlinarith only [hp,hq]
