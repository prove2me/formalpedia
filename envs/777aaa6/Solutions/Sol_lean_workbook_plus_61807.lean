-- Prove2me | solution 1 for lean_workbook_plus_61807
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:11.801967+00:00
-- url     : https://prove2.me/submissions/34ba609b-130f-401f-a218-08bf807013a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x + b)
  (h₁ : f 2 = 3)
  (h₂ : f 3 = 2) :
  a^2 + b^2 = 26 := by
  intros
  grind
