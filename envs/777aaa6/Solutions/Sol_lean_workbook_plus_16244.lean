-- Prove2me | solution 1 for lean_workbook_plus_16244
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:53.577089+00:00
-- url     : https://prove2.me/submissions/4625814b-bf68-498c-acc3-7207f72a7e6c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a>0 ∧ b>0 ∧ c>0 ∧ a+b+c=3) : a^4+b^4+c^4 ≥ a^3+b^3+c^3 := by
  intros
  have p2m_cond_3 : (a+b+c : ℝ) = (3) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (3) - (a+b+c) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (a^4+b^4+c^4) - (a^3+b^3+c^3) = ((1 / 6) : ℝ) * 1 * (((a ^ 2) + ((-1) * a * b)))^2 + ((1 / 6) : ℝ) * 1 * (((a ^ 2) + ((-1) * a * c)))^2 + ((1 / 6) : ℝ) * 1 * (((a ^ 2) + ((-1) * (b ^ 2))))^2 + ((1 / 6) : ℝ) * 1 * (((a ^ 2) + ((-1) * (c ^ 2))))^2 + ((1 / 6) : ℝ) * 1 * ((((-1) * (b ^ 2)) + (a * b)))^2 + ((1 / 6) : ℝ) * 1 * ((((-1) * (c ^ 2)) + (a * c)))^2 + ((1 / 6) : ℝ) * 1 * (((b ^ 2) + ((-1) * b * c)))^2 + ((1 / 6) : ℝ) * 1 * (((b ^ 2) + ((-1) * (c ^ 2))))^2 + ((1 / 6) : ℝ) * 1 * ((((-1) * (c ^ 2)) + (b * c)))^2 := by
    linear_combination ((((-1 / 3) * (a ^ 3)) + ((-1 / 3) * (b ^ 3)) + ((-1 / 3) * (c ^ 3)))) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (a^4+b^4+c^4) - (a^3+b^3+c^3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
