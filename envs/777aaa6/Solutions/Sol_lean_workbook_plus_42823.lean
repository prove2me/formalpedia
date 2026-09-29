-- Prove2me | solution 1 for lean_workbook_plus_42823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:31.205494+00:00
-- url     : https://prove2.me/submissions/7650415d-bb29-46c2-83cd-d8cd4a15651f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 8 * a * b * c ≥ (a + b) * (b + c) * (c + a) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (a^3 + b^3 + c^3 + 8 * a * b * c) - ((a + b) * (b + c) * (c + a)) = (1 : ℝ) * ((a) - (0)) * ((a + ((-1) * b) + ((-1) * c)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + c + ((-1) * b)))^2 + (1 : ℝ) * ((c) - (0)) * ((a + b + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^3 + b^3 + c^3 + 8 * a * b * c) - ((a + b) * (b + c) * (c + a)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
