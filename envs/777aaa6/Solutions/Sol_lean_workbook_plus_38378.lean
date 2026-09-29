-- Prove2me | solution 1 for lean_workbook_plus_38378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:09.645399+00:00
-- url     : https://prove2.me/submissions/875a13e2-1ee6-40ce-ac68-90b3a352fc2a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - x - 6 = 0 ↔ x = 3 ∨ x = -2 := by
  intros
  grind
