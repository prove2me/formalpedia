-- Prove2me | solution 1 for lean_workbook_plus_73006
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:03.005005+00:00
-- url     : https://prove2.me/submissions/b1216cea-665a-4e27-8e43-3348d97afdc9

import Mathlib

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z := by
  intro x y z
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
