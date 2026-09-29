-- Prove2me | solution 1 for lean_workbook_plus_4520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:10.367166+00:00
-- url     : https://prove2.me/submissions/541ffd7a-1586-4b0f-bde8-8548305cd981

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (b : ℝ) : (1 + b) ^ 2 ≥ 4 * b ↔ (1 - b) ^ 2 ≥ 0 := by
  intros
  grind
