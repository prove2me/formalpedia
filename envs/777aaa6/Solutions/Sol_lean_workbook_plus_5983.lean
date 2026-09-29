-- Prove2me | solution 1 for lean_workbook_plus_5983
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:45.742088+00:00
-- url     : https://prove2.me/submissions/d7ad232d-7889-442a-8617-ab180515acef

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * Real.sqrt ((a^2 * b + b^2 * c + c^2 * a) * (a + b + c)) ≥ 2 * (a * b + b * c + c * a) := by
  have hp1 := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (a-c))
  have hp2 := mul_nonneg (mul_nonneg hb.le hc.le) (sq_nonneg (b-a))
  have hp3 := mul_nonneg (mul_nonneg hc.le ha.le) (sq_nonneg (c-b))
  have hs : a*b+b*c+c*a≤Real.sqrt ((a^2*b+b^2*c+c^2*a)*(a+b+c)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hp1,hp2,hp3]
  linarith
