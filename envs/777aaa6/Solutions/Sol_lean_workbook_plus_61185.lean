-- Prove2me | solution 1 for lean_workbook_plus_61185
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:32.81359+00:00
-- url     : https://prove2.me/submissions/8dbd89f7-7061-4194-bfb6-bdfe81a7a85e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c > 0) :
  (a - b + c) * (1 / (a + b) - 1 / (b + c) + 1 / (c + a)) ≤ 1 / 2 := by
  intros
  have hc0 : 0 < c := by aesop
  have hb0 : 0 < b := by grind
  have ha0 : 0 < a := by grind
  have p2m_cond_0 : (b : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (b) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (c : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (c) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (((-2) * (c ^ 3)) + (2 * (a ^ 3)) + (2 * (b ^ 3)) + (a * (b ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-3) * a * (c ^ 2)) + ((-3) * b * (a ^ 2))) = ((39 / 55) : ℝ) * ((a) - (b)) * ((a + ((-1) * b)))^2 + ((71 / 55) : ℝ) * ((a) - (b)) * ((a + ((-1) * c)))^2 + ((3 / 44) : ℝ) * ((b) - (c)) * ((a + (2 * b)))^2 + ((7 / 20) : ℝ) * ((b) - (c)) * ((a + ((-2) * b)))^2 + ((3 / 4) : ℝ) * ((b) - (c)) * ((b + (2 * c)))^2 + ((63 / 220) : ℝ) * ((b) - (c)) * ((b + ((-2) * c)))^2 + ((102 / 55) : ℝ) * ((c) - (0)) * ((a + ((-1) * b)))^2 + ((118 / 55) : ℝ) * ((c) - (0)) * ((a + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((-2) * (c ^ 3)) + (2 * (a ^ 3)) + (2 * (b ^ 3)) + (a * (b ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-3) * a * (c ^ 2)) + ((-3) * b * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (a + b) * (a + c) * (b + c)) := by first | positivity | nlinarith | aesop
  have h_rational : (1 / 2) - ((a - b + c) * (1 / (a + b) - 1 / (b + c) + 1 / (c + a))) = ((((-2) * (c ^ 3)) + (2 * (a ^ 3)) + (2 * (b ^ 3)) + (a * (b ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-3) * a * (c ^ 2)) + ((-3) * b * (a ^ 2)))) / ((2 * (a + b) * (a + c) * (b + c))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
