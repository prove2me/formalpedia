-- Prove2me | solution 1 for lean_workbook_plus_28648
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:42.119264+00:00
-- url     : https://prove2.me/submissions/db4fb81a-b6dc-477a-9f78-4c5c12b47734

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x = (1 + Real.sqrt 5) / 2) : x^2 = x + 1 ∧ 1/x = x - 1 := by
  intros
  grind
