-- Prove2me | solution 1 for lean_workbook_plus_26642
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:43.390275+00:00
-- url     : https://prove2.me/submissions/2e18f1f6-4ed3-4b94-a75e-f514fa7c57b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (N : ℤ) (M : ℤ) (h₁ : M = (N - 376) / 3) : M = (N - 376) / 3 := by
  (intros; simp_all)
