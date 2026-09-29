-- Prove2me | solution 1 for lean_workbook_plus_59589
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:40.466342+00:00
-- url     : https://prove2.me/submissions/39dba312-d066-44dd-aca7-fb06c12c6da2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : -3 * x ^ 2 - 3 * x + 3 / 2 = 0 ↔ x = -1 / 2 + Real.sqrt 3 / 2 ∨ x = -1 / 2 - Real.sqrt 3 / 2 := by
  intros
  grind
