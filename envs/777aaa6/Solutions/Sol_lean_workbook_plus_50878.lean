-- Prove2me | solution 1 for lean_workbook_plus_50878
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:47.773091+00:00
-- url     : https://prove2.me/submissions/51b52be0-efe8-4c99-b99f-8bc733c215b9

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a)   := by
  intro a b c
  linarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]

#print axioms solution
