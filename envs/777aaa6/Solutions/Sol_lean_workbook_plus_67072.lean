-- Prove2me | solution 1 for lean_workbook_plus_67072
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:18.33859+00:00
-- url     : https://prove2.me/submissions/01b7134c-53cb-4da8-9863-80f65ea2119d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a ≠ b)
  (h₂ : ∀ x < -1 - b / a, f x = 0)
  (h₃ : ∀ x, -1 - b / a ≤ x ∧ x ≤ -2 → f x = a / (a - b) * x + 2 * a / (a - b))
  (h₄ : ∀ x > -2, f x = 1) :
  ∀ x, f x = if x < -1 - b / a then 0 else if -1 - b / a ≤ x ∧ x ≤ -2 then a / (a - b) * x + 2 * a / (a - b) else 1 := by
  intros
  grind
