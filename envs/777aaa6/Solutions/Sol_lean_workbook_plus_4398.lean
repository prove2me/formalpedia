-- Prove2me | solution 1 for lean_workbook_plus_4398
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:55.44852+00:00
-- url     : https://prove2.me/submissions/953a0d37-14f1-4eb6-9be2-038e6087132b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : 5*x+5*y+2*x*y=-19) (h₂ : x+y+3*x*y=-35) : x = -3 ∧ y = 4 ∨ x = 4 ∧ y = -3 := by
  intros
  grind
