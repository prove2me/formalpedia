-- Prove2me | solution 1 for lean_workbook_plus_1355
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:02.947848+00:00
-- url     : https://prove2.me/submissions/c1b9e18e-3652-4d08-885e-a633a5e67d7e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y / (x * y + y + 1) + z / (y * z + z + 1) + x / (z * x + x + 1)) ≤ 1 := by
  intros
  
  have h_identity : (1 + ((x ^ 2) * (y ^ 2) * (z ^ 2)) + ((-2) * x * y * z)) = (1 : ℝ) * 1 * ((1 + ((-1) * x * y * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + ((x ^ 2) * (y ^ 2) * (z ^ 2)) + ((-2) * x * y * z)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + x + (x * z)) * (1 + y + (x * y)) * (1 + z + (y * z))) := by positivity
  have h_rational : (1) - ((y / (x * y + y + 1) + z / (y * z + z + 1) + x / (z * x + x + 1))) = ((1 + ((x ^ 2) * (y ^ 2) * (z ^ 2)) + ((-2) * x * y * z))) / (((1 + x + (x * z)) * (1 + y + (x * y)) * (1 + z + (y * z)))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
