-- Prove2me | solution 1 for lean_workbook_plus_28998
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:13.784056+00:00
-- url     : https://prove2.me/submissions/0d357626-4298-4cf9-8793-54af7076b506

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z^2 / x^2 + (x^2 + y^2) / (2 * z^2)) ≥ 1 + y / x := by
  intros
  
  have h_identity : ((x ^ 4) + (2 * (z ^ 4)) + ((x ^ 2) * (y ^ 2)) + ((-2) * (x ^ 2) * (z ^ 2)) + ((-2) * x * y * (z ^ 2))) = (1 : ℝ) * 1 * (((x ^ 2) + ((-1) * (z ^ 2))))^2 + (1 : ℝ) * 1 * ((((-1) * (z ^ 2)) + (x * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x ^ 4) + (2 * (z ^ 4)) + ((x ^ 2) * (y ^ 2)) + ((-2) * (x ^ 2) * (z ^ 2)) + ((-2) * x * y * (z ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (x ^ 2) * (z ^ 2)) := by positivity
  have h_rational : ((z^2 / x^2 + (x^2 + y^2) / (2 * z^2))) - (1 + y / x) = (((x ^ 4) + (2 * (z ^ 4)) + ((x ^ 2) * (y ^ 2)) + ((-2) * (x ^ 2) * (z ^ 2)) + ((-2) * x * y * (z ^ 2)))) / ((2 * (x ^ 2) * (z ^ 2))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
