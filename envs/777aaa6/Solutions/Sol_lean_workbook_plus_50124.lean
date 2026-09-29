-- Prove2me | solution 1 for lean_workbook_plus_50124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:43.328288+00:00
-- url     : https://prove2.me/submissions/a70645b0-1c4d-423d-8348-f0e44ceb168e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^4 + b^4 + 2 ≥ 4 * a * b := by
  intros
  
  have h_identity : (a^4 + b^4 + 2) - (4 * a * b) = (2 : ℝ) * 1 * ((1 + ((-1) * a * b)))^2 + (1 : ℝ) * 1 * (((a ^ 2) + ((-1) * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^4 + b^4 + 2) - (4 * a * b) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
