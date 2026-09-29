-- Prove2me | solution 1 for lean_workbook_plus_27656
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:38.231593+00:00
-- url     : https://prove2.me/submissions/9b147198-5cb4-47fe-a887-50455301dd7e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2 + 2 * a * b) * (4 + 1) ≥ (2 * a + 2 * b + c)^2 := by
  intros
  
  have h_identity : ((a^2 + b^2 + c^2 + 2 * a * b) * (4 + 1)) - ((2 * a + 2 * b + c)^2) = (1 : ℝ) * 1 * ((a + b + ((-2) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2 + 2 * a * b) * (4 + 1)) - ((2 * a + 2 * b + c)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
