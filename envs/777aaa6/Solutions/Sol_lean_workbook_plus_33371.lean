-- Prove2me | solution 1 for lean_workbook_plus_33371
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:26.328453+00:00
-- url     : https://prove2.me/submissions/0f399a25-6dc7-45f0-9f9b-f7822fdf471c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ z : ℂ, ‖3 * z ^ 2 + 12 * z‖ ≤ ‖3 * z ^ 2‖ + ‖12 * z‖ := by
  intro z
  intros
  exact norm_add_le (3 * z ^ 2) (12 * z)
