-- Prove2me | solution 1 for lean_workbook_plus_65235
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:35.292217+00:00
-- url     : https://prove2.me/submissions/ec10d807-664e-46a1-a208-55c5a78f9d50

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) :
  3 * x^4 + 1 ≥ 4 * x^3 := by
  intros
  
  have h_identity : (3 * x^4 + 1) - (4 * x^3) = (1 : ℝ) * 1 * ((1 + ((-1) * (x ^ 2))))^2 + (2 : ℝ) * 1 * ((x + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (3 * x^4 + 1) - (4 * x^3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
