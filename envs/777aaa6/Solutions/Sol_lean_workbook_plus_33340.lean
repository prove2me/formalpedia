-- Prove2me | solution 1 for lean_workbook_plus_33340
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:27.606643+00:00
-- url     : https://prove2.me/submissions/f2c2e6b2-70a2-4b5b-9407-48f59c080888

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (y : ℝ) : 5*y^2 + 2 = 7*y ↔ y = 1 ∨ y = 2/5 := by
  intros
  grind
