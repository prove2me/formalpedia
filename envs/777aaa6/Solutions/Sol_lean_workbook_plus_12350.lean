-- Prove2me | solution 1 for lean_workbook_plus_12350
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:01.565707+00:00
-- url     : https://prove2.me/submissions/fb47b314-6195-4d17-abe0-e82d0953e31e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a*b^4 + 2*b^2*c^3 >= 4*a*b^2*c^2 := by
  have h1 : 0 ≤ a * (a * c - b ^ 2) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have h2 : 0 ≤ 2 * b ^ 2 * c * (a - c) ^ 2 := by positivity
  nlinarith only [h1, h2]
