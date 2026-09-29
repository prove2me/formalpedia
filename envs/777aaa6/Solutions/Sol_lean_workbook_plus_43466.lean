-- Prove2me | solution 1 for lean_workbook_plus_43466
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:53.789519+00:00
-- url     : https://prove2.me/submissions/faaec0c9-925e-413e-b461-cb70ff6793bd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c > 0 ∧ a + b + c = 1) :
  b / (b + c) + c / (c + a) + a / (a + b) ≥ 3 / 2 := by
  intros
  have p2m_pos_a : (0 : ℝ) < a := by grind
  have p2m_pos_b : (0 : ℝ) < b := by grind
  have p2m_pos_c : (0 : ℝ) < c := by grind
  
  have p2m_cond_0 : (b : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (b) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (c : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (c) := by linarith only [p2m_cond_1]
  have h_identity : ((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))) = (1 : ℝ) * ((a) - (b)) * ((b + ((-1) * c)))^2 + (1 : ℝ) * ((b) - (c)) * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (a + b) * (a + c) * (b + c)) := by positivity
  have h_rational : (b / (b + c) + c / (c + a) + a / (a + b)) - (3 / 2) = (((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2)))) / ((2 * (a + b) * (a + c) * (b + c))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
