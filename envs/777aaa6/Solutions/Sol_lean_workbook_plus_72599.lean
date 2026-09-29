-- Prove2me | solution 1 for lean_workbook_plus_72599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:54.354356+00:00
-- url     : https://prove2.me/submissions/8f5fc949-d336-4358-bc49-a35c772c5d97

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ t : ℝ, 4 * t ^ 4 + 2 * t ^ 3 + 3 * t ^ 2 - 4 * t + 1 > 0 := by
  intro t
  have hi : 4*t^4+2*t^3+3*t^2-4*t+1 = (2*t^2+t/2-1/2)^2 + (19/4)*(t-7/19)^2 + 2/19 := by ring
  rw [hi]
  positivity
