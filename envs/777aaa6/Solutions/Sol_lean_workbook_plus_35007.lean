-- Prove2me | solution 1 for lean_workbook_plus_35007
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:27.774284+00:00
-- url     : https://prove2.me/submissions/d5390b76-cb77-4799-9049-7fc342955186

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : 2 * (a * b + b * c + c * a) + a ^ 2 + b ^ 2 + c ^ 2 ≥ 0 := by
  intros
  
  have h_identity : (2 * (a * b + b * c + c * a) + a ^ 2 + b ^ 2 + c ^ 2) - (0) = (1 : ℝ) * 1 * ((a + b + c))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 * (a * b + b * c + c * a) + a ^ 2 + b ^ 2 + c ^ 2) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
