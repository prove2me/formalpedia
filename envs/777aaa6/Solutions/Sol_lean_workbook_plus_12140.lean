-- Prove2me | solution 1 for lean_workbook_plus_12140
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:21.744018+00:00
-- url     : https://prove2.me/submissions/2b318e15-2bf1-4c29-b37f-61734a2792b7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 + a^4) * (1 + b^4) * (1 + c^4) * (1 + d^4) ≥ 1 + (a * b * c * d)^4 := by
  have pair (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 1+u*v ≤ (1+u)*(1+v) := by nlinarith
  have h1 := pair (a^4) (b^4) (by positivity) (by positivity)
  have h2 := pair (c^4) (d^4) (by positivity) (by positivity)
  have hprod := mul_le_mul h1 h2 (show 0 ≤ 1+c^4*d^4 by positivity) (show 0 ≤ (1+a^4)*(1+b^4) by positivity)
  have h3 := pair (a^4*b^4) (c^4*d^4) (by positivity) (by positivity)
  simp only [mul_pow]
  nlinarith only [hprod,h3]
