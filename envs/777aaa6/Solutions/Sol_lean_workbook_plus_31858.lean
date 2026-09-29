-- Prove2me | solution 1 for lean_workbook_plus_31858
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:54.444947+00:00
-- url     : https://prove2.me/submissions/11a7d472-fe09-4a32-8f1c-18b3090361d4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 2 ≤ x) : (x^2 - x + 6)^2 ≥ 16 * (3 * x - 2) := by
  intros
  
  have h_identity : ((x^2 - x + 6)^2) - (16 * (3 * x - 2)) = (68 : ℝ) * 1 * ((1 + ((-15 / 34) * x) + ((-1 / 34) * (x ^ 2))))^2 + ((64 / 17) : ℝ) * 1 * ((x + ((-1 / 2) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x^2 - x + 6)^2) - (16 * (3 * x - 2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
