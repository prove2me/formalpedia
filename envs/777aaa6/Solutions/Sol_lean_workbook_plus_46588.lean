-- Prove2me | solution 1 for lean_workbook_plus_46588
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:47.882913+00:00
-- url     : https://prove2.me/submissions/3fb59e76-6c06-4845-acee-b5d4cb318972

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (h : x^3 + y^3 + z^3 = 3) : x*y*z + 8 ≥ 3 * (x*y + y*z + z*x) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (z) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (z) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (x^3 + y^3 + z^3 : ℝ) = (3) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (3) - (x^3 + y^3 + z^3) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (x*y*z + 8) - (3 * (x*y + y*z + z*x)) = (3 : ℝ) * 1 * ((1 + ((-1 / 3) * x) + ((-1 / 3) * y) + ((-1 / 3) * z)))^2 + (2 : ℝ) * ((x) - (0)) * ((1 + ((-11 / 24) * y) + ((-11 / 24) * z) + ((-1 / 12) * x)))^2 + ((119 / 72) : ℝ) * ((x) - (0)) * ((x + ((-1 / 2) * y) + ((-1 / 2) * z)))^2 + ((2 / 3) : ℝ) * ((x) - (0)) * ((y + ((-1) * z)))^2 + (2 : ℝ) * ((y) - (0)) * ((1 + ((-11 / 24) * x) + ((-11 / 24) * z) + ((-1 / 12) * y)))^2 + ((311 / 288) : ℝ) * ((y) - (0)) * ((x + ((-238 / 311) * y) + ((-73 / 311) * z)))^2 + ((952 / 933) : ℝ) * ((y) - (0)) * ((y + ((-1) * z)))^2 + (2 : ℝ) * ((z) - (0)) * ((1 + ((-11 / 24) * x) + ((-11 / 24) * y) + ((-1 / 12) * z)))^2 + ((311 / 288) : ℝ) * ((z) - (0)) * ((x + ((-238 / 311) * z) + ((-73 / 311) * y)))^2 + ((952 / 933) : ℝ) * ((z) - (0)) * ((y + ((-1) * z)))^2 := by
    linear_combination ((5 / 3)) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (x*y*z + 8) - (3 * (x*y + y*z + z*x)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
