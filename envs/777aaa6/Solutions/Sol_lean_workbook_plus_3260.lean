-- Prove2me | solution 1 for lean_workbook_plus_3260
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:50.610505+00:00
-- url     : https://prove2.me/submissions/900bf25d-2178-45c0-bd72-95e65d18681d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 + 3*x - 40 = 0 ↔ x = 5 ∨ x = -8 := by
  intros
  grind
