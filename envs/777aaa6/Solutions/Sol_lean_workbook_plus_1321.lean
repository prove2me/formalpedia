-- Prove2me | solution 1 for lean_workbook_plus_1321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:15.330509+00:00
-- url     : https://prove2.me/submissions/c846ec3a-f345-41e2-9cea-1dc26bca2716

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℝ → ℝ)
  (h₀ : StrictAnti f)
  (h₁ : f 0 = 1)
  (h₂ : f 1 = 0)
  : ∀ x ∈ Set.Ioo 0 1, 0 < f x ∧ f x < 1 := by
  intro x hx
  constructor
  · simpa [h₂] using h₀ hx.2
  · simpa [h₁] using h₀ hx.1
