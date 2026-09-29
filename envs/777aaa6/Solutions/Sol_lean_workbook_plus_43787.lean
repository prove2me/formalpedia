-- Prove2me | solution 1 for lean_workbook_plus_43787
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:46.157735+00:00
-- url     : https://prove2.me/submissions/0cce2c27-32d6-4f3f-bbff-d9bc6cf16b29

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 / 2)
  (h₁ : ∀ x, ∀ y, f (x + y) + f (x - y) = (x + y)^2 / 2 + (x - y)^2 / 2) :
  f (x + y) + f (x - y) = x^2 + y^2 := by
  intros
  grind
