-- Prove2me | solution 1 for lean_workbook_plus_14053
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:11.684622+00:00
-- url     : https://prove2.me/submissions/6feb823d-3d7e-4a3d-aa57-3173e1723c70

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b / c + b / a / c + c / a / b ≥ 2 / a + 2 / b - 2 / c := by
  intros
  
  have h_identity : ((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-2) * a * c) + ((-2) * b * c) + (2 * a * b)) = (1 : ℝ) * 1 * ((a + b + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-2) * a * c) + ((-2) * b * c) + (2 * a * b)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c) := by positivity
  have h_rational : (a / b / c + b / a / c + c / a / b) - (2 / a + 2 / b - 2 / c) = (((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-2) * a * c) + ((-2) * b * c) + (2 * a * b))) / ((a * b * c)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
