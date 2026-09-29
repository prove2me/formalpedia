-- Prove2me | solution 1 for lean_workbook_plus_48592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:30.38669+00:00
-- url     : https://prove2.me/submissions/3d8e27c9-7cb6-4533-ba75-4061de54f73b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 15*x + 56 = 0 ↔ x = 7 ∨ x = 8 := by
  intros
  grind
