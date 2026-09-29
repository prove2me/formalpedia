-- Prove2me | solution 1 for lean_workbook_plus_861
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:15.370412+00:00
-- url     : https://prove2.me/submissions/acbc4a82-242d-4caf-89a7-20f1d15d17e6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 2*x^2*y + 2*x*y^2 + x^2 + y^2 + 2*x*y + 1 - x*y ≥ 3*(2*x*y + x + y)/2 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have h_identity : (2*x^2*y + 2*x*y^2 + x^2 + y^2 + 2*x*y + 1 - x*y) - (3*(2*x*y + x + y)/2) = (1 : ℝ) * 1 * ((1 + ((-1) * x) + ((-1) * y)))^2 + ((1 / 2) : ℝ) * ((x) - (0)) * ((1 + ((-2) * y)))^2 + ((1 / 2) : ℝ) * ((y) - (0)) * ((1 + ((-2) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2*x^2*y + 2*x*y^2 + x^2 + y^2 + 2*x*y + 1 - x*y) - (3*(2*x*y + x + y)/2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
