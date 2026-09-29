-- Prove2me | solution 1 for lean_workbook_plus_48644
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:29.453338+00:00
-- url     : https://prove2.me/submissions/7dd05136-f63e-4ef4-899d-705351c7b689

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ)
  (p : ℝ → ℝ)
  (h₀ : ∀ x, p x = (x + 1) * (x - 4) * (x - 2) + a * x^2 + b * x + c)
  (h₁ : p (-1) = 2)
  (h₂ : p 4 = -13)
  (h₃ : p 2 = 5) :
  a - b + c = 2 ∧ 16 * a + 4 * b + c = -13 ∧ 4 * a + 2 * b + c = 5 := by
  intros
  grind
