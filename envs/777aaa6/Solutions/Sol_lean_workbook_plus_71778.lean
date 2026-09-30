-- Prove2me | solution 1 for lean_workbook_plus_71778
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:15:42.334889+00:00
-- url     : https://prove2.me/submissions/0d62c1c8-e1ba-4f30-93ad-795c228be0cb

import Mathlib
set_option autoImplicit false

theorem solution : ∀ (a b c : ℝ), a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a   := by
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

#print axioms solution
