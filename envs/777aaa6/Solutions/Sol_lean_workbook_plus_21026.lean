-- Prove2me | solution 1 for lean_workbook_plus_21026
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:12.039133+00:00
-- url     : https://prove2.me/submissions/87c96880-24b4-460a-9f0b-823315530d03

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a + b)^2 + b^2 / (b + c)^2 + c / (c + a)) ≥ 1 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((c * (b ^ 4)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((-1) * a * (b ^ 2) * (c ^ 2)) + ((-2) * c * (a ^ 2) * (b ^ 2))) = (1 : ℝ) * ((a) - (0)) * (((a * b) + ((-1) * b * c)))^2 + (1 : ℝ) * ((c) - (0)) * ((((-1) * (b ^ 2)) + (a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((c * (b ^ 4)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((-1) * a * (b ^ 2) * (c ^ 2)) + ((-2) * c * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (((a + b) ^ 2) * ((b + c) ^ 2) * (a + c)) := by positivity
  have h_rational : ((a^2 / (a + b)^2 + b^2 / (b + c)^2 + c / (c + a))) - (1) = (((c * (b ^ 4)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((-1) * a * (b ^ 2) * (c ^ 2)) + ((-2) * c * (a ^ 2) * (b ^ 2)))) / ((((a + b) ^ 2) * ((b + c) ^ 2) * (a + c))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
