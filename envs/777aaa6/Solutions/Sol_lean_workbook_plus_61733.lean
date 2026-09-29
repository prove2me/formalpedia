-- Prove2me | solution 1 for lean_workbook_plus_61733
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:20.37215+00:00
-- url     : https://prove2.me/submissions/589593ac-5a19-482b-a200-991798e43bbc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (a : ℝ) (ha : a = x^2 + 4*x + 8) : (1 / (Real.sqrt (x^2 + 4*x + 13) + Real.sqrt (x^2 + 4*x + 8))) = 1 / 10 ↔ (1 / (Real.sqrt a + Real.sqrt (a + 5))) = 1 / 10 := by
  intros
  grind
