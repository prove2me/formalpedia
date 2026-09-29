-- Prove2me | solution 1 for lean_workbook_plus_37721
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:26.07488+00:00
-- url     : https://prove2.me/submissions/c2ff0ae5-c3da-4b42-aa74-cad0f202068b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : (x = 3 ∧ y = 4) → (7 * x - 4 * y) / (3 * x + y) = 5 / 13 := by
  intros
  grind
