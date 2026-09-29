-- Prove2me | solution 1 for lean_workbook_plus_69480
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:10.920491+00:00
-- url     : https://prove2.me/submissions/d23af54a-adc3-4bde-a813-44b4d5b8dc6a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℝ) (hn : n ≠ 0) : ((n + 2) / (6 * n) : ℝ) = 1 / 5 ↔ n = 10 := by
  intros
  grind
