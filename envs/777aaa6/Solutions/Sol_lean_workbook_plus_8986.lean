-- Prove2me | solution 1 for lean_workbook_plus_8986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:39.834397+00:00
-- url     : https://prove2.me/submissions/6ed2ad3f-d5ec-4788-ace3-cf3125f17350

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c p : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hp : p ≥ 0) : (a + b * p) ^ 2 + (b + c * p) ^ 2 + (c + a * p) ^ 2 ≥ (1 + p) ^ 2 / 2 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) := by
  have hs : 0 ≤ a^2+b^2+c^2-a*b-b*c-c*a := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hm := mul_nonneg (sq_nonneg (p-1)) hs
  nlinarith only [hm]
