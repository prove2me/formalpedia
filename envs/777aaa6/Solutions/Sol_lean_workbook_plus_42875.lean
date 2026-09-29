-- Prove2me | solution 1 for lean_workbook_plus_42875
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:58.700307+00:00
-- url     : https://prove2.me/submissions/4834b65f-6b0c-4c8b-8f60-2e2ee65543fa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) : (a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 ∧ (a = b ∧ b = c ∧ c = 3 / 2)) ↔ a = b ∧ b = c ∧ c = 3 / 2 := by
  constructor
  · exact And.right
  · intro h
    have heq : a / (b+c) + b / (c+a) + c / (a+b) = 3/2 := by grind
    exact ⟨le_of_eq heq.symm, h⟩
