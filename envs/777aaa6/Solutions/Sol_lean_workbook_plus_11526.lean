-- Prove2me | solution 1 for lean_workbook_plus_11526
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:27.150215+00:00
-- url     : https://prove2.me/submissions/65a90819-0e51-4b92-8d46-38cd306cfc96

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^2 + b^2 + a * b) * (b^2 + c^2 + b * c) * (c^2 + a^2 + c * a) ≥ 3 * (a * b^2 + b * c^2 + c * a^2) * (a^2 * b + b^2 * c + c^2 * a) := by
  intros
  
  have h_identity : ((a^2 + b^2 + a * b) * (b^2 + c^2 + b * c) * (c^2 + a^2 + c * a)) - (3 * (a * b^2 + b * c^2 + c * a^2) * (a^2 * b + b^2 * c + c^2 * a)) = (1 : ℝ) * 1 * (((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + a * b) * (b^2 + c^2 + b * c) * (c^2 + a^2 + c * a)) - (3 * (a * b^2 + b * c^2 + c * a^2) * (a^2 * b + b^2 * c + c^2 * a)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
