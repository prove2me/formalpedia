-- Prove2me | solution 1 for lean_workbook_plus_14764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:41.919813+00:00
-- url     : https://prove2.me/submissions/6ab2503f-1016-471c-a8c0-166100d880b4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 5*x + 5 = -1 ↔ x = 2 ∨ x = 3 := by
  intros
  grind
