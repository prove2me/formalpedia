-- Prove2me | solution 1 for lean_workbook_plus_14892
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:35.592493+00:00
-- url     : https://prove2.me/submissions/688124ed-b379-471c-aba7-05c0282fc7b7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2 + a * c + b * a + a * c)^2 ≥ 4 * (a^2 + b^2 + c^2) * (a * c + b * a + a * c) := by
  intros
  
  have h_identity : ((a^2 + b^2 + c^2 + a * c + b * a + a * c)^2) - (4 * (a^2 + b^2 + c^2) * (a * c + b * a + a * c)) = (1 : ℝ) * 1 * (((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-1) * a * b) + ((-2) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2 + a * c + b * a + a * c)^2) - (4 * (a^2 + b^2 + c^2) * (a * c + b * a + a * c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
