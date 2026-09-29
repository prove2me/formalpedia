-- Prove2me | solution 1 for lean_workbook_plus_60532
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:39.386136+00:00
-- url     : https://prove2.me/submissions/9954d59f-533a-439e-bbc2-240a0c8761e6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : (x + y + z) ^ 2 * (x*y + y*z + z*x) ^ 2 ≤ 3 * (x ^ 2 + x*y + y ^ 2) * (y ^ 2 + y*z + z ^ 2) * (z ^ 2 + z*x + x ^ 2) := by
  intros
  
  have h_identity : (3 * (x ^ 2 + x*y + y ^ 2) * (y ^ 2 + y*z + z ^ 2) * (z ^ 2 + z*x + x ^ 2)) - ((x + y + z) ^ 2 * (x*y + y*z + z*x) ^ 2) = (2 : ℝ) * 1 * (((y * (x ^ 2)) + ((-1 / 2) * x * (z ^ 2)) + ((-1 / 2) * y * (z ^ 2)) + ((-1 / 2) * z * (y ^ 2)) + ((1 / 4) * x * (y ^ 2)) + ((1 / 4) * z * (x ^ 2))))^2 + ((15 / 8) : ℝ) * 1 * (((z * (x ^ 2)) + ((-3 / 5) * x * (y ^ 2)) + ((-2 / 5) * y * (z ^ 2)) + ((-2 / 5) * z * (y ^ 2)) + ((2 / 5) * x * (z ^ 2))))^2 + ((6 / 5) : ℝ) * 1 * (((x * (y ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1 / 4) * x * (z ^ 2)) + ((1 / 4) * z * (y ^ 2))))^2 + ((9 / 8) : ℝ) * 1 * (((x * (z ^ 2)) + ((-1) * z * (y ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (3 * (x ^ 2 + x*y + y ^ 2) * (y ^ 2 + y*z + z ^ 2) * (z ^ 2 + z*x + x ^ 2)) - ((x + y + z) ^ 2 * (x*y + y*z + z*x) ^ 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
