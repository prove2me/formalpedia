-- Prove2me | solution 1 for lean_workbook_plus_59628
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:56.374928+00:00
-- url     : https://prove2.me/submissions/ac2b40e7-4e8d-4a33-9b1e-81018544754a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 7/3 * x - 2 = 0 ↔ x = 3 ∨ x = -2/3 := by
  intros
  grind
