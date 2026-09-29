-- Prove2me | solution 1 for lean_workbook_plus_75525
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:01.399084+00:00
-- url     : https://prove2.me/submissions/0f11fb0e-ccba-449e-9d09-b6feae947b77

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k : ℝ) : 2 ≤ abs (1 + k) + 2 * abs (1 - k) := by
  intros
  grind
