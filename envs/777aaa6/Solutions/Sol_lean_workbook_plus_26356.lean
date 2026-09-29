-- Prove2me | solution 1 for lean_workbook_plus_26356
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:16.749294+00:00
-- url     : https://prove2.me/submissions/623f34fa-3cc0-4371-90fa-c29908323880

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (f_def : ∀ x, f x = x^2 + x + 1) : f (-1) + f 0 + f 1 = 5 := by
  (intros; simp_all)
