-- Prove2me | solution 1 for lean_workbook_plus_41503
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:37.043491+00:00
-- url     : https://prove2.me/submissions/e4d9bf8f-5495-448e-b700-4c43c840a33b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b x y : ℝ) (h₀ : 0 < y) (h₁ : y ≤ 3 * x) :  x * (a^4 + b^4) + 2 * y * a^2 * b^2 ≥ (x + y) * (a^3 * b + a * b^3) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (y : ℝ) ≤ (3 * x) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (3 * x) - (y) := by linarith only [p2m_cond_1]
  have h_identity : (x * (a^4 + b^4) + 2 * y * a^2 * b^2) - ((x + y) * (a^3 * b + a * b^3)) = ((1 / 3) : ℝ) * ((y) - (0)) * (((a ^ 2) + (b ^ 2) + ((-2) * a * b)))^2 + ((1 / 3) : ℝ) * ((3 * x) - (y)) * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * a * b)))^2 + ((1 / 4) : ℝ) * ((3 * x) - (y)) * ((((-1) * (b ^ 2)) + (a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x * (a^4 + b^4) + 2 * y * a^2 * b^2) - ((x + y) * (a^3 * b + a * b^3)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
