-- Prove2me | solution 1 for lean_workbook_plus_3379
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:57.253923+00:00
-- url     : https://prove2.me/submissions/991ba116-c587-4a03-aade-208128c5dbb9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) : 3 * (1 + a^2 + a^4) ≥ (1 + a + a^2)^2 := by
  intros
  
  have h_identity : (3 * (1 + a^2 + a^4)) - ((1 + a + a^2)^2) = (2 : ℝ) * 1 * ((1 + ((-1 / 2) * a) + ((-1 / 2) * (a ^ 2))))^2 + ((3 / 2) : ℝ) * 1 * ((a + ((-1) * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (3 * (1 + a^2 + a^4)) - ((1 + a + a^2)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
