-- Prove2me | solution 1 for lean_workbook_plus_37737
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:09.449277+00:00
-- url     : https://prove2.me/submissions/12099bb4-0ff6-41ef-a642-36e8edd6fdf5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : 4 * (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ≥ 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2 := by
  intros
  
  have h_identity : (4 * (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2)) - (3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2) = (1 : ℝ) * 1 * (((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (4 * (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2)) - (3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
