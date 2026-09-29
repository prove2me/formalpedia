-- Prove2me | solution 1 for lean_workbook_plus_66830
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:50.147225+00:00
-- url     : https://prove2.me/submissions/12bfebac-8fa3-4a7f-999c-e0fd1304efda

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a₁ a₂ : ℝ) : (6*a₁ + a₂ = -27 ∧ 3*a₁ + 2*a₂ = -2) ↔ a₁ = -52/9 ∧ a₂ = 23/3 := by
  intros
  grind
