-- Prove2me | solution 1 for lean_workbook_plus_48552
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:40.144226+00:00
-- url     : https://prove2.me/submissions/b4716915-9d12-4f0e-822b-ac057739ad79

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / a ^ 2 + 1 / b ≥ 4 / (a ^ 2 + b) := by
  intros
  
  have h_identity : ((a ^ 4) + (b ^ 2) + ((-2) * b * (a ^ 2))) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 4) + (b ^ 2) + ((-2) * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (b * (a ^ 2) * (b + (a ^ 2))) := by positivity
  have h_rational : (1 / a ^ 2 + 1 / b) - (4 / (a ^ 2 + b)) = (((a ^ 4) + (b ^ 2) + ((-2) * b * (a ^ 2)))) / ((b * (a ^ 2) * (b + (a ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
