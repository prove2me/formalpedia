-- Prove2me | solution 1 for lean_workbook_plus_24867
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:59.938278+00:00
-- url     : https://prove2.me/submissions/c174ca4b-29ae-4342-9e41-f9f4f1306b9c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (h : x * y * z - 3 = x + y + z) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ x ^ 2 * y ^ 2 * z ^ 2 - 6 * (x + y + z) - 9 := by
  intros
  have p2m_cond_0 : (x * y * z - 3 : ℝ) = (x + y + z) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (x + y + z) - (x * y * z - 3) = 0 := by linarith only [p2m_cond_0]
  have h_identity : (3 * (x ^ 2 + y ^ 2 + z ^ 2)) - (x ^ 2 * y ^ 2 * z ^ 2 - 6 * (x + y + z) - 9) = (1 : ℝ) * 1 * ((x + ((-1) * y)))^2 + (1 : ℝ) * 1 * ((x + ((-1) * z)))^2 + (1 : ℝ) * 1 * ((y + ((-1) * z)))^2 := by
    linear_combination ((3 + x + y + z + (x * y * z))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2)) - (x ^ 2 * y ^ 2 * z ^ 2 - 6 * (x + y + z) - 9) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
