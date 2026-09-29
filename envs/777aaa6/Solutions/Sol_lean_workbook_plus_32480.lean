-- Prove2me | solution 1 for lean_workbook_plus_32480
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:49.403409+00:00
-- url     : https://prove2.me/submissions/4e3cb677-4efe-494f-a96a-6187153db7f5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ)
  (h₀ : (x^2 / 16 + y^2 / 9) = 1)
  (h₁ : x = (12 - 4 * y) / 3) :
  x = 0 ∧ y = 3 ∨ x = 4 ∧ y = 0 := by
  intros
  grind
