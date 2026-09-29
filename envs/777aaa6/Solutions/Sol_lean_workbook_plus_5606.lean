-- Prove2me | solution 1 for lean_workbook_plus_5606
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:29.07675+00:00
-- url     : https://prove2.me/submissions/ebb4f249-78d7-4039-bbe4-e8cd0bf66e3b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (habc : a * b * c = 1) : 1 / (2 * a ^ 2 + b ^ 2 + 3) + 1 / (2 * b ^ 2 + c ^ 2 + 3) + 1 / (2 * c ^ 2 + a ^ 2 + 3) ≤ 1 / 2 := by
  intros
  have p2m_cond_0 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((-27) + ((-9) * (a ^ 2)) + ((-9) * (b ^ 2)) + ((-9) * (c ^ 2)) + (2 * (a ^ 4)) + (2 * (b ^ 4)) + (2 * (c ^ 4)) + (2 * (a ^ 2) * (b ^ 4)) + (2 * (a ^ 4) * (c ^ 2)) + (2 * (b ^ 2) * (c ^ 4)) + (4 * (a ^ 2) * (c ^ 4)) + (4 * (a ^ 4) * (b ^ 2)) + (4 * (b ^ 4) * (c ^ 2)) + (7 * (a ^ 2) * (b ^ 2)) + (7 * (a ^ 2) * (c ^ 2)) + (7 * (b ^ 2) * (c ^ 2)) + (9 * (a ^ 2) * (b ^ 2) * (c ^ 2))) = (2 : ℝ) * 1 * ((1 + ((-1) * (b ^ 2))))^2 + (2 : ℝ) * 1 * ((1 + ((-1) * (c ^ 2))))^2 + (3 : ℝ) * 1 * ((a + ((-1) * b * c)))^2 + (2 : ℝ) * 1 * (((a ^ 2) + ((-1) * a * b * c)))^2 + (2 : ℝ) * 1 * (((b * (a ^ 2)) + ((-1) * a * c)))^2 + (2 : ℝ) * 1 * (((b * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + (2 : ℝ) * 1 * (((c * (a ^ 2)) + ((-1) * a * b)))^2 + (4 : ℝ) * 1 * (((a * b) + ((-1) * c * (b ^ 2))))^2 + (1 : ℝ) * 1 * ((((-1) * c) + (a * b)))^2 + (1 : ℝ) * 1 * (((a * (b ^ 2)) + ((-1) * a * (c ^ 2))))^2 + (1 : ℝ) * 1 * (((a * (b ^ 2)) + ((-1) * b * c)))^2 + (5 : ℝ) * 1 * ((((-1) * b) + (a * c)))^2 + (3 : ℝ) * 1 * (((a * (c ^ 2)) + ((-1) * b * c)))^2 := by
    linear_combination (((-31) + ((-12) * (a ^ 2)) + ((-10) * (b ^ 2)) + ((-6) * (c ^ 2)) + ((-13) * a * b * c))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((-27) + ((-9) * (a ^ 2)) + ((-9) * (b ^ 2)) + ((-9) * (c ^ 2)) + (2 * (a ^ 4)) + (2 * (b ^ 4)) + (2 * (c ^ 4)) + (2 * (a ^ 2) * (b ^ 4)) + (2 * (a ^ 4) * (c ^ 2)) + (2 * (b ^ 2) * (c ^ 4)) + (4 * (a ^ 2) * (c ^ 4)) + (4 * (a ^ 4) * (b ^ 2)) + (4 * (b ^ 4) * (c ^ 2)) + (7 * (a ^ 2) * (b ^ 2)) + (7 * (a ^ 2) * (c ^ 2)) + (7 * (b ^ 2) * (c ^ 2)) + (9 * (a ^ 2) * (b ^ 2) * (c ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (3 + (a ^ 2) + (2 * (c ^ 2))) * (3 + (b ^ 2) + (2 * (a ^ 2))) * (3 + (c ^ 2) + (2 * (b ^ 2)))) := by positivity
  have h_rational : (1 / 2) - (1 / (2 * a ^ 2 + b ^ 2 + 3) + 1 / (2 * b ^ 2 + c ^ 2 + 3) + 1 / (2 * c ^ 2 + a ^ 2 + 3)) = (((-27) + ((-9) * (a ^ 2)) + ((-9) * (b ^ 2)) + ((-9) * (c ^ 2)) + (2 * (a ^ 4)) + (2 * (b ^ 4)) + (2 * (c ^ 4)) + (2 * (a ^ 2) * (b ^ 4)) + (2 * (a ^ 4) * (c ^ 2)) + (2 * (b ^ 2) * (c ^ 4)) + (4 * (a ^ 2) * (c ^ 4)) + (4 * (a ^ 4) * (b ^ 2)) + (4 * (b ^ 4) * (c ^ 2)) + (7 * (a ^ 2) * (b ^ 2)) + (7 * (a ^ 2) * (c ^ 2)) + (7 * (b ^ 2) * (c ^ 2)) + (9 * (a ^ 2) * (b ^ 2) * (c ^ 2)))) / ((2 * (3 + (a ^ 2) + (2 * (c ^ 2))) * (3 + (b ^ 2) + (2 * (a ^ 2))) * (3 + (c ^ 2) + (2 * (b ^ 2))))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
