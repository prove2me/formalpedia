-- Prove2me | solution 1 for lean_workbook_plus_7907
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:08.062285+00:00
-- url     : https://prove2.me/submissions/244fa79c-a9fc-4727-84dc-5db8f40f076a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x : ℝ, x^3 ≥ x ↔ x * (x^2 - 1) ≥ 0 := by
  intro x
  intros
  grind
