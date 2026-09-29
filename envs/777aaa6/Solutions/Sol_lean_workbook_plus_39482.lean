-- Prove2me | solution 1 for lean_workbook_plus_39482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:40.336886+00:00
-- url     : https://prove2.me/submissions/c0fab628-6a32-4f0b-9119-67e9ba01a6ee

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution :  ∀ a b c : ℝ, c ≥ b ∧ b ≥ a ∧ a ≥ 0 → (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  intro a b c
  intros
  have p2m_cond_0 : (b : ℝ) ≤ (c) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (c) - (b) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (a : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (a) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((a + 3 * b) * (b + 4 * c) * (c + 2 * a)) - (60 * a * b * c) = ((5 / 3) : ℝ) * ((c) - (b)) * ((a + b))^2 + ((4 / 27) : ℝ) * ((c) - (b)) * ((a + (2 * b)))^2 + ((14 / 27) : ℝ) * ((b) - (a)) * ((a + ((-2) * b)))^2 + ((76 / 27) : ℝ) * ((b) - (a)) * ((a + ((-2) * c)))^2 + ((5 / 27) : ℝ) * ((b) - (a)) * ((b + (2 * c)))^2 + ((43 / 54) : ℝ) * ((a) - (0)) * ((a + ((-1) * b)))^2 + ((137 / 54) : ℝ) * ((a) - (0)) * ((a + ((-1) * c)))^2 + ((727 / 54) : ℝ) * ((a) - (0)) * ((b + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a + 3 * b) * (b + 4 * c) * (c + 2 * a)) - (60 * a * b * c) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
