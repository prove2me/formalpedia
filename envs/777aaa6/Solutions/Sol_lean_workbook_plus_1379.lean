-- Prove2me | solution 1 for lean_workbook_plus_1379
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:56.215412+00:00
-- url     : https://prove2.me/submissions/961ed901-36d9-40e6-9b41-aadd2244714b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  intros
  have p2m_cond_3 : (c : ℝ) < (a + b) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (a + b) - (c) := by linarith only [p2m_cond_3]
  have p2m_cond_4 : (a : ℝ) < (b + c) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (0 : ℝ) ≤ (b + c) - (a) := by linarith only [p2m_cond_4]
  have p2m_cond_5 : (b : ℝ) < (a + c) := by first | assumption | aesop | linarith
  have p2m_cond_5_gap : (0 : ℝ) ≤ (a + c) - (b) := by linarith only [p2m_cond_5]
  have h_identity : (3 * a * b * c) - (a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c)) = ((1 / 2) : ℝ) * ((a + b) - (c)) * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((b + c) - (a)) * ((b + ((-1) * c)))^2 + ((1 / 2) : ℝ) * ((a + c) - (b)) * ((a + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (3 * a * b * c) - (a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
