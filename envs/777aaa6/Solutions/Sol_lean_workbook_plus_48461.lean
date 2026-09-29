-- Prove2me | solution 1 for lean_workbook_plus_48461
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:52.521909+00:00
-- url     : https://prove2.me/submissions/2095f0ab-4cf2-49a1-a624-eca37a3ee487

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : abs a + abs b + abs c + abs (a + b + c) ≥ abs (a + b) + abs (b + c) + abs (c + a) := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith
