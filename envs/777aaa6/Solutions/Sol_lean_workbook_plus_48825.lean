-- Prove2me | solution 1 for lean_workbook_plus_48825
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:24.027128+00:00
-- url     : https://prove2.me/submissions/7b6227a0-1ef4-4f2d-ad12-1304176ce032

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (k : ℝ) : k^2 - 20 * k + 100 ≥ 0 := by
  intros
  
  have h_identity : (k^2 - 20 * k + 100) - (0) = (100 : ℝ) * 1 * ((1 + ((-1 / 10) * k)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (k^2 - 20 * k + 100) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
