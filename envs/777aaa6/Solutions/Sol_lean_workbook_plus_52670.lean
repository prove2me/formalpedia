-- Prove2me | solution 1 for lean_workbook_plus_52670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:21.169612+00:00
-- url     : https://prove2.me/submissions/aa2368bc-a3c7-40a3-8e05-bd0a279e7edf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : a^2 * (a - (b + c))^2 + a^2 * (b^2 + c^2) + (b^2 + c^2) * (b - c)^2 ≥ 2 * a * (b + c) * (b - c)^2 := by
  intros
  
  have h_identity : (a^2 * (a - (b + c))^2 + a^2 * (b^2 + c^2) + (b^2 + c^2) * (b - c)^2) - (2 * a * (b + c) * (b - c)^2) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1) * a * b) + ((-1) * a * c)))^2 + (1 : ℝ) * 1 * ((((-1) * (b ^ 2)) + (a * b) + (b * c)))^2 + (1 : ℝ) * 1 * ((((-1) * (c ^ 2)) + (a * c) + (b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 * (a - (b + c))^2 + a^2 * (b^2 + c^2) + (b^2 + c^2) * (b - c)^2) - (2 * a * (b + c) * (b - c)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
