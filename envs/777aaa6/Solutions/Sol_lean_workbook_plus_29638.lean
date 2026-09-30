-- Prove2me | solution 1 for lean_workbook_plus_29638
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:58:11.094035+00:00
-- url     : https://prove2.me/submissions/d09449e0-8571-4a05-8f05-7d689b21555f

import Mathlib
set_option autoImplicit false

theorem solution : ∀ t : ℝ, t ∈ Set.Icc 0 (1 / 2) → 4 * t ^ 2 + 8 * t - 5 ≤ 0   := by
  rintro t ⟨ht0, ht1⟩
  have hp : (2 * t - 1) * (2 * t + 5) <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  nlinarith only [hp]

#print axioms solution
