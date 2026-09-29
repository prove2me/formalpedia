-- Prove2me | solution 1 for lean_workbook_plus_3904
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:18.176421+00:00
-- url     : https://prove2.me/submissions/3a0c21a4-409b-4141-8d00-9d6d54ed5f4f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ)
  (f : ℕ → ℝ)
  (h₀ : ∀ a, f a = a^2 * x + (a + 1)^2 * y + (a + 2)^2 * z)
  (h₁ : f 1 = 305)
  (h₂ : f 2 = 319)
  (h₃ : f 3 = 880) :
  f 4 = 1988 := by
  intros
  grind
