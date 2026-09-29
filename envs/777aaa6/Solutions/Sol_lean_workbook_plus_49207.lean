-- Prove2me | solution 1 for lean_workbook_plus_49207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:51.036051+00:00
-- url     : https://prove2.me/submissions/88891477-6b8f-4e80-b10f-6a904ee1b716

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ 1) : x^4 + y^4 - x^2*y - x*y^2 ≥ -1/8 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (x + y : ℝ) ≤ (1) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (1) - (x + y) := by linarith only [p2m_cond_2]
  have h_identity : (x^4 + y^4 - x^2*y - x*y^2) - (-1/8) = ((17 / 200) : ℝ) * 1 * ((1 + ((-2) * x)))^2 + ((17 / 100) : ℝ) * 1 * ((x + ((-2) * (x ^ 2))))^2 + ((4 / 25) : ℝ) * 1 * ((x + ((-2) * x * y)))^2 + ((17 / 100) : ℝ) * 1 * ((x + ((-2) * (y ^ 2))))^2 + ((8 / 25) : ℝ) * 1 * (((x ^ 2) + ((-1) * (y ^ 2))))^2 + ((11 / 50) : ℝ) * ((x) - (0)) * ((1 + ((-2) * x)))^2 + ((1 / 25) : ℝ) * ((y) - (0)) * ((1 + ((-2) * y)))^2 + ((1 / 25) : ℝ) * ((1) - (x + y)) * ((1 + (2 * x)))^2 + ((1 / 25) : ℝ) * ((1) - (x + y)) * ((x + (2 * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^4 + y^4 - x^2*y - x*y^2) - (-1/8) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
