-- Prove2me | solution 1 for lean_workbook_plus_58532
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:12.96501+00:00
-- url     : https://prove2.me/submissions/89861d41-2ba4-459f-b9fb-e2d660fcbc13

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, c * (c + a) + b * (a + b) = (a + b) * (c + a) ↔ a^2 = b^2 + c^2 - b * c := by
  intro a b c
  intros
  grind
