-- Prove2me | solution 1 for lean_workbook_plus_13792
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:13.584881+00:00
-- url     : https://prove2.me/submissions/b3fa81c7-0cff-4038-ba7e-19a43b62158d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y : ℝ, x^6 + y^5 ≤ x + 1 ↔ y^5 ≤ x + 1 - x^6 := by
  intro x y
  intros
  exact?
