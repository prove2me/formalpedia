-- Prove2me | solution 1 for lean_workbook_plus_20581
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:22.80627+00:00
-- url     : https://prove2.me/submissions/aff42569-f3b4-4fc5-bc1b-0085a14932a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ)
  (h₀ : f 0 = -1)
  (h₁ : f (Real.sqrt 5) = -1)
  (h₂ : ∀ t ∈ Set.Icc 0 (Real.sqrt 5), f t ≤ -1) :
  ∀ t ∈ Set.Icc 0 (Real.sqrt 5), 1 ≤ |f t| := by
  intros
  grind
