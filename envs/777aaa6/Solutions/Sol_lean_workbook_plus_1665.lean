-- Prove2me | solution 1 for lean_workbook_plus_1665
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:18.546097+00:00
-- url     : https://prove2.me/submissions/e2d2feb8-4699-4fc2-aa74-ab911910932b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h : a - b = 4) : a * c + b * c - c ^ 2 - a * b ≤ 4 := by
  have p2m_attained : ∃ a b c : ℝ, a-b=4 ∧ a*c+b*c-c^2-a*b=4 := by
    refine ⟨4,0,2,?_⟩
    norm_num
  intros
  have p2m_cond_0 : (a - b : ℝ) = (4) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (4) - (a - b) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (4) - (a * c + b * c - c ^ 2 - a * b) = ((1 / 4) : ℝ) * 1 * ((a + b + ((-2) * c)))^2 := by
    linear_combination ((1 + ((-1 / 4) * b) + ((1 / 4) * a))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (4) - (a * c + b * c - c ^ 2 - a * b) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
