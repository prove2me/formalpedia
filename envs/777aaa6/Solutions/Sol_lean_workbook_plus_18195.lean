-- Prove2me | solution 1 for lean_workbook_plus_18195
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:50.100246+00:00
-- url     : https://prove2.me/submissions/3427d251-ae4d-4b29-8482-290009920cc2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx: 0 ≤ x ∧ x ≤ 3) :
  x * (3 - x) / (7 - x) ≤ 2 / 9 * x + 1 / 9 := by
  intros
  have hx3 : x ≤ 3 := by aesop
  have hfac : 0 < 7-x := by linarith
  
  have h_identity : (7 + ((-14) * x) + (7 * (x ^ 2))) = (7 : ℝ) * 1 * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (7 + ((-14) * x) + (7 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((-9) * ((-7) + x)) := by first | positivity | nlinarith | aesop
  have h_rational : (2 / 9 * x + 1 / 9) - (x * (3 - x) / (7 - x)) = ((7 + ((-14) * x) + (7 * (x ^ 2)))) / (((-9) * ((-7) + x))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
