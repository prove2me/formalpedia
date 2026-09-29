-- Prove2me | solution 1 for lean_workbook_plus_63262
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:17.431896+00:00
-- url     : https://prove2.me/submissions/30ee3c99-e9bd-41d6-9816-80b16154cd3b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 6*x + 8 = 0 ↔ x = 4 ∨ x = 2 := by
  intros
  grind
