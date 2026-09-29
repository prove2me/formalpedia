-- Prove2me | solution 1 for lean_workbook_plus_52971
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:59.655785+00:00
-- url     : https://prove2.me/submissions/9bdb9af0-f5e4-47b3-a534-c7009d7c5572

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b c : ℝ} (h : a + b + c = 0) :
  (a^2 + b^2 + c^2)^3 ≥ 2 * (a - b)^2 * (b - c)^2 * (c - a)^2 := by
  intros
  have p2m_cond_0 : (a + b + c : ℝ) = (0) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0) - (a + b + c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((a^2 + b^2 + c^2)^3) - (2 * (a - b)^2 * (b - c)^2 * (c - a)^2) = (48 : ℝ) * 1 * ((a * b * c))^2 + (2 : ℝ) * 1 * (((a * (b ^ 2)) + (b * (a ^ 2))))^2 + (2 : ℝ) * 1 * (((a * (c ^ 2)) + (c * (a ^ 2))))^2 + (2 : ℝ) * 1 * (((b * (c ^ 2)) + (c * (b ^ 2))))^2 := by
    linear_combination ((((-1) * (a ^ 5)) + ((-1) * (b ^ 5)) + ((-1) * (c ^ 5)) + (a * (b ^ 4)) + (a * (c ^ 4)) + (b * (a ^ 4)) + (b * (c ^ 4)) + (c * (a ^ 4)) + (c * (b ^ 4)) + ((-6) * a * b * (c ^ 3)) + ((-6) * a * c * (b ^ 3)) + ((-6) * b * c * (a ^ 3)) + (10 * a * (b ^ 2) * (c ^ 2)) + (10 * b * (a ^ 2) * (c ^ 2)) + (10 * c * (a ^ 2) * (b ^ 2)))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2)^3) - (2 * (a - b)^2 * (b - c)^2 * (c - a)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
