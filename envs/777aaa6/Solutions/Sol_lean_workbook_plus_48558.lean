-- Prove2me | solution 1 for lean_workbook_plus_48558
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:45.855929+00:00
-- url     : https://prove2.me/submissions/af4b4aa2-9cf5-467c-8899-c09783b04a10

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ y : ℝ, y^2 + y + 1 + 2 * Real.sqrt (y^2 + y) ≥ y^2 - y ↔ 2 * y + 1 + 2 * Real.sqrt (y^2 + y) ≥ 0 := by
  intro y
  intros
  grind
