-- Prove2me | solution 1 for lean_workbook_plus_19418
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:00.935035+00:00
-- url     : https://prove2.me/submissions/75647f8f-3bca-4fd5-87c7-20fd9b32858a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (c : ℤ) (h : ∀ x, f (x + 1) = c * f x - f (x - 1)) : ∀ x, f (x + 1) = c * f x - f (x - 1) := by
  (intros; simp_all)
