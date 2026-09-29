-- Prove2me | solution 1 for lean_workbook_plus_14932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:22.509192+00:00
-- url     : https://prove2.me/submissions/2e84897a-1063-4662-b33c-2cafa784af31

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ m : ℕ, (1 : ℝ) / (m + 1) < 1 / (3 * m + 2) + 1 / (3 * m + 3) + 1 / (3 * m + 4) := by
  intro m
  have hm : 0 ≤ (m:ℝ) := by positivity
  have hi : 1/(3*(m:ℝ)+2)+1/(3*(m:ℝ)+3)+1/(3*(m:ℝ)+4)-1/((m:ℝ)+1) = 2/(3*((m:ℝ)+1)*(3*(m:ℝ)+2)*(3*(m:ℝ)+4)) := by field_simp; ring
  have hp : 0 < 2/(3*((m:ℝ)+1)*(3*(m:ℝ)+2)*(3*(m:ℝ)+4)) := by positivity
  linarith
