-- Prove2me | solution 1 for lean_workbook_plus_43212
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:26.730118+00:00
-- url     : https://prove2.me/submissions/38a4b18a-430a-4de8-a497-b5d44ef3a4d8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  3 * (a ^ 2 + b ^ 2 + c ^ 2) / (2 * (a * b + b * c + a * c)) ≥ a / (b + c) + b / (a + c) + c / (b + a) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((a * (b ^ 4)) + (a * (c ^ 4)) + (b * (a ^ 4)) + (b * (c ^ 4)) + (c * (a ^ 4)) + (c * (b ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((b ^ 3) * (c ^ 2)) + ((-4) * a * (b ^ 2) * (c ^ 2)) + ((-4) * b * (a ^ 2) * (c ^ 2)) + ((-4) * c * (a ^ 2) * (b ^ 2))) = (1 : ℝ) * ((a) - (0)) * ((((-1) * (c ^ 2)) + (a * b)))^2 + (1 : ℝ) * ((a) - (0)) * ((((-1) * (b ^ 2)) + (a * c)))^2 + (1 : ℝ) * ((b) - (0)) * (((a ^ 2) + ((-1) * b * c)))^2 + (1 : ℝ) * ((b) - (0)) * ((((-1) * (c ^ 2)) + (a * b)))^2 + (1 : ℝ) * ((c) - (0)) * (((a ^ 2) + ((-1) * b * c)))^2 + (1 : ℝ) * ((c) - (0)) * ((((-1) * (b ^ 2)) + (a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a * (b ^ 4)) + (a * (c ^ 4)) + (b * (a ^ 4)) + (b * (c ^ 4)) + (c * (a ^ 4)) + (c * (b ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((b ^ 3) * (c ^ 2)) + ((-4) * a * (b ^ 2) * (c ^ 2)) + ((-4) * b * (a ^ 2) * (c ^ 2)) + ((-4) * c * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (a + b) * (a + c) * (b + c) * ((a * b) + (a * c) + (b * c))) := by positivity
  have h_rational : (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (2 * (a * b + b * c + a * c))) - (a / (b + c) + b / (a + c) + c / (b + a)) = (((a * (b ^ 4)) + (a * (c ^ 4)) + (b * (a ^ 4)) + (b * (c ^ 4)) + (c * (a ^ 4)) + (c * (b ^ 4)) + ((a ^ 2) * (b ^ 3)) + ((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((b ^ 3) * (c ^ 2)) + ((-4) * a * (b ^ 2) * (c ^ 2)) + ((-4) * b * (a ^ 2) * (c ^ 2)) + ((-4) * c * (a ^ 2) * (b ^ 2)))) / ((2 * (a + b) * (a + c) * (b + c) * ((a * b) + (a * c) + (b * c)))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
