-- Prove2me | solution 1 for lean_workbook_plus_30628
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:51.182484+00:00
-- url     : https://prove2.me/submissions/b8afe40c-e6c4-4704-a5a3-e631b5286190

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) : (b^2+c^2+d^2+a^2)^2 >= b^2 * (b+d) * (c+a) + c^2 * (c+a) * (b+d) + d^2 * (b+d) * (c+a) + a^2 * (c+a) * (b+d) := by
  have hs : 0≤b^2+c^2+d^2+a^2 := by positivity
  have hq : 0≤b^2+c^2+d^2+a^2-(b+d)*(c+a) := by nlinarith only [sq_nonneg (b-d),sq_nonneg (c-a),sq_nonneg (b+d-c-a)]
  have hp := mul_nonneg hs hq
  nlinarith only [hp]
