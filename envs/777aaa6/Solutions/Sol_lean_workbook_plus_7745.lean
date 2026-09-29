-- Prove2me | solution 1 for lean_workbook_plus_7745
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:13.048019+00:00
-- url     : https://prove2.me/submissions/a3a0b950-30ea-404a-bb90-1b0bcaae460c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c d : ℝ, a + b + c + d = 0 → a^3 + b^3 + c^3 + d^3 = 3 * (a * b * c + b * c * d + c * d * a + d * a * b) := by
  intro a b c d
  intros
  grind
