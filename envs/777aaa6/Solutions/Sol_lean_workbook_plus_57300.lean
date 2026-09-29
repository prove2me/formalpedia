-- Prove2me | solution 1 for lean_workbook_plus_57300
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:00.393427+00:00
-- url     : https://prove2.me/submissions/c978affe-1e22-4b62-9de7-09c9dc073044

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a*b^4 + 2*b^2*c^3 ≥ 4*a*b^2*c^2 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (a^3*c^2 + a*b^4 + 2*b^2*c^3) - (4*a*b^2*c^2) = (1 : ℝ) * ((a) - (0)) * ((((-1) * (b ^ 2)) + (a * c)))^2 + (2 : ℝ) * ((c) - (0)) * (((a * b) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^3*c^2 + a*b^4 + 2*b^2*c^3) - (4*a*b^2*c^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
