-- Prove2me | solution 1 for lean_workbook_plus_23970
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:31:36.60068+00:00
-- url     : https://prove2.me/submissions/1f51d38f-a98d-43e5-9ebd-bd33a0f4413e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx: x ≥ 2) : x^8 + x^7 - x^5 - x^4 - x^3 + x + 1 > x^8 := by
  have hx0 : 0 ≤ x := by linarith
  have hp : 0 ≤ x^4-x^2-x-1 := by
    have h := mul_nonneg (show 0 ≤ x-2 by linarith)
      (show 0 ≤ x^3+2*x^2+3*x+5 by positivity)
    nlinarith only [h]
  have hm := mul_nonneg (pow_nonneg hx0 3) hp
  nlinarith only [hx, hm]
