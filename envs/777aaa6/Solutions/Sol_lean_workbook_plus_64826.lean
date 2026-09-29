-- Prove2me | solution 1 for lean_workbook_plus_64826
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:25.785539+00:00
-- url     : https://prove2.me/submissions/4c5bba97-4ea1-490f-834e-b1aac8842d90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (h : x + y = 0 ∧ y + z = 0 ∧ z + x = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  intros
  grind
