-- Prove2me | solution 1 for lean_workbook_plus_72289
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:13.570991+00:00
-- url     : https://prove2.me/submissions/035b6efd-a1d0-410b-be58-0cb88de3c24a

import Mathlib

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x ^ 2 + 2 * x + 1 ≥ 0 := by
  intro x
  nlinarith [sq_nonneg (x + 1)]
