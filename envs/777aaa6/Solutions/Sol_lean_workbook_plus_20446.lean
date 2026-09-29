-- Prove2me | solution 1 for lean_workbook_plus_20446
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:11:07.73813+00:00
-- url     : https://prove2.me/submissions/1344bc52-a3d2-462c-8605-275e594ea5d6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) : 8 * (a * b * c * d + 1) > (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  have hu : 0 < a-1 := by linarith
  have hv : 0 < b-1 := by linarith
  have hw : 0 < c-1 := by linarith
  have ht : 0 < d-1 := by linarith
  have h1 := mul_pos hu hv
  have h2 := mul_pos hu hw
  have h3 := mul_pos hu ht
  have h4 := mul_pos hv hw
  have h5 := mul_pos hv ht
  have h6 := mul_pos hw ht
  have h7 := mul_pos h1 hw
  have h8 := mul_pos h1 ht
  have h9 := mul_pos h2 ht
  have h10 := mul_pos h4 ht
  have h11 := mul_pos h7 ht
  nlinarith
