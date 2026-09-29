-- Prove2me | solution 1 for lean_workbook_plus_12052
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:29.505406+00:00
-- url     : https://prove2.me/submissions/d8316ba4-6051-4769-b13d-ebb5ef812dc1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * a + b * b + c * c = d * d) : x * x + y * y + z * z ≥ (a * x + b * y + c * z) ^ 2 / d ^ 2 := by
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have he : d^2=a^2+b^2+c^2 := by nlinarith
  rw [he]
  nlinarith only [sq_nonneg (a*y-b*x), sq_nonneg (a*z-c*x), sq_nonneg (b*z-c*y)]
