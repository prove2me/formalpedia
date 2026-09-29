-- Prove2me | solution 1 for lean_workbook_plus_20277
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:37.238353+00:00
-- url     : https://prove2.me/submissions/2a559fb7-8b91-49d2-988d-9af623c4caf1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (h : ∀ x, 2 * f x + 3 * f (-x) = x^2 + 5 * x) : f 7 = -126 / 5 := by
  intros
  grind
