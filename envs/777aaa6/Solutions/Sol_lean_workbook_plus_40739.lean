-- Prove2me | solution 1 for lean_workbook_plus_40739
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:51.537874+00:00
-- url     : https://prove2.me/submissions/df12fd51-4464-445e-896e-5bdd00c9a494

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (h : a + b + c + d = 1) : a * b + a * c + a * d + b * c + b * d + c * d ≤ 3 / 8 := by
  intros
  have p2m_cond_0 : (a + b + c + d : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (1) - (a + b + c + d) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (3 / 8) - (a * b + a * c + a * d + b * c + b * d + c * d) = ((1 / 8) : ℝ) * 1 * ((a + ((-1) * b)))^2 + ((1 / 8) : ℝ) * 1 * ((a + ((-1) * c)))^2 + ((1 / 8) : ℝ) * 1 * ((a + ((-1) * d)))^2 + ((1 / 8) : ℝ) * 1 * ((b + ((-1) * c)))^2 + ((1 / 8) : ℝ) * 1 * ((b + ((-1) * d)))^2 + ((1 / 8) : ℝ) * 1 * ((c + ((-1) * d)))^2 := by
    linear_combination (((3 / 8) + ((3 / 8) * a) + ((3 / 8) * b) + ((3 / 8) * c) + ((3 / 8) * d))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (3 / 8) - (a * b + a * c + a * d + b * c + b * d + c * d) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
