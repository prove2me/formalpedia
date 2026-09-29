-- Prove2me | solution 1 for lean_workbook_plus_58803
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:40.223031+00:00
-- url     : https://prove2.me/submissions/c3c93dd5-cfe9-466b-b152-3372e69ad119

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n p q : ℤ)
  (f : ℤ → ℤ)
  (h₀ : ∀ x, f x = (x - p) * (x - q))
  (h₁ : p = n - 13)
  (h₂ : q = n - 1)
  (h₃ : n + 1 = 15) :
  f (n + 1) = 28 := by
  intros
  grind
