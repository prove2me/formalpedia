-- Prove2me | solution 1 for lean_workbook_plus_37542
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:05.166052+00:00
-- url     : https://prove2.me/submissions/c7738f83-457d-4a55-8c60-96d5000b7c58

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 + 5*x + 6 = 0 ↔ x = -3 ∨ x = -2 := by
  intros
  grind
