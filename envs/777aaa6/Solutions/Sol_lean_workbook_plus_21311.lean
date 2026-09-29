-- Prove2me | solution 1 for lean_workbook_plus_21311
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:36.440149+00:00
-- url     : https://prove2.me/submissions/29858c8c-8a81-4906-9996-90b2161603f0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 + 3*x + 1 = 0 ↔ x = (-3 + Real.sqrt 5)/2 ∨ x = (-3 - Real.sqrt 5)/2 := by
  intros
  grind
