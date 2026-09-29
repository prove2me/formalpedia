-- Prove2me | solution 1 for lean_workbook_plus_60010
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:39.555127+00:00
-- url     : https://prove2.me/submissions/5009c61c-94d2-47e0-bcaf-0f15b2cc9a73

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) :
  (x + y - z) * (z + x - y) * (x - y) * (x - z) + (y + z - x) * (x + y - z) * (y - z) * (y - x) + (z + x - y) * (y + z - x) * (z - x) * (z - y) ≥ 0 := by
  intros
  
  have h_identity : ((x + y - z) * (z + x - y) * (x - y) * (x - z) + (y + z - x) * (x + y - z) * (y - z) * (y - x) + (z + x - y) * (y + z - x) * (z - x) * (z - y)) - (0) = (1 : ℝ) * 1 * (((x ^ 2) + ((-1 / 2) * (y ^ 2)) + ((-1 / 2) * (z ^ 2)) + (y * z) + ((-1 / 2) * x * y) + ((-1 / 2) * x * z)))^2 + ((3 / 4) : ℝ) * 1 * (((z ^ 2) + ((-1) * (y ^ 2)) + (x * y) + ((-1) * x * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x + y - z) * (z + x - y) * (x - y) * (x - z) + (y + z - x) * (x + y - z) * (y - z) * (y - x) + (z + x - y) * (y + z - x) * (z - x) * (z - y)) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
