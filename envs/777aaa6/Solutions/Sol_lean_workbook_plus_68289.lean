-- Prove2me | solution 1 for lean_workbook_plus_68289
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:59.149036+00:00
-- url     : https://prove2.me/submissions/318679b4-2a00-4ec8-a3f8-8521a5fb3082

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 + (2 * x^2 / z^2) + (3 * y^2 / x^2) ≥ 2 * y / x + 4 * y / z := by
  intros
  
  have h_identity : ((2 * (x ^ 4)) + ((x ^ 2) * (z ^ 2)) + (3 * (y ^ 2) * (z ^ 2)) + ((-4) * y * z * (x ^ 2)) + ((-2) * x * y * (z ^ 2))) = (2 : ℝ) * 1 * (((x ^ 2) + ((-1) * y * z)))^2 + (1 : ℝ) * 1 * (((x * z) + ((-1) * y * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (x ^ 4)) + ((x ^ 2) * (z ^ 2)) + (3 * (y ^ 2) * (z ^ 2)) + ((-4) * y * z * (x ^ 2)) + ((-2) * x * y * (z ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((x ^ 2) * (z ^ 2)) := by positivity
  have h_rational : (1 + (2 * x^2 / z^2) + (3 * y^2 / x^2)) - (2 * y / x + 4 * y / z) = (((2 * (x ^ 4)) + ((x ^ 2) * (z ^ 2)) + (3 * (y ^ 2) * (z ^ 2)) + ((-4) * y * z * (x ^ 2)) + ((-2) * x * y * (z ^ 2)))) / (((x ^ 2) * (z ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
