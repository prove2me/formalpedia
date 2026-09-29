-- Prove2me | solution 1 for lean_workbook_plus_4319
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:54.646143+00:00
-- url     : https://prove2.me/submissions/351c93a9-3b0e-43be-ba10-d20109b4af7a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : 2*a^2 - 2*a*(b + c - 3) + 2*(b^2 + c^2) - 2*b*c + 6*(1 - b) ≥ 0 := by
  intros
  
  have h_identity : (2*a^2 - 2*a*(b + c - 3) + 2*(b^2 + c^2) - 2*b*c + 6*(1 - b)) - (0) = (6 : ℝ) * 1 * ((1 + ((1 / 2) * a) + ((-1 / 2) * b)))^2 + ((1 / 2) : ℝ) * 1 * ((a + b + ((-2) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2*a^2 - 2*a*(b + c - 3) + 2*(b^2 + c^2) - 2*b*c + 6*(1 - b)) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
