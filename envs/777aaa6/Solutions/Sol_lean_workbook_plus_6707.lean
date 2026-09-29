-- Prove2me | solution 1 for lean_workbook_plus_6707
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:22.825513+00:00
-- url     : https://prove2.me/submissions/197d4ed8-0c11-4ecb-95d0-91e9e54f3ded

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b)
  (h₁ : a ≤ b) :
  a / (1 + a) ≤ b / (1 + b) := by
  intros
  have ha0 : 0 ≤ a := by aesop
  have hb0 : 0 ≤ b := by aesop
  have p2m_cond_2 : (a : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (b) - (a) := by linarith only [p2m_cond_2]
  have h_identity : (b + ((-1) * a)) = (1 : ℝ) * ((b) - (a)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (b + ((-1) * a)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + a) * (1 + b)) := by first | positivity | nlinarith | aesop
  have h_rational : (b / (1 + b)) - (a / (1 + a)) = ((b + ((-1) * a))) / (((1 + a) * (1 + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
