-- Prove2me | solution 1 for lean_workbook_plus_46630
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:26.147557+00:00
-- url     : https://prove2.me/submissions/64ece4c2-bc10-464a-b4b1-9a8b23c98ae5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a^2 + b^2 + c^2 ≥ (1 / 3) * (a + b + c)^2 ↔ a^2 + b^2 + c^2 ≥ b * c + c * a + a * b := by
  intro a b c
  intros
  grind
