-- Prove2me | solution 1 for lean_workbook_plus_46526
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:03.407289+00:00
-- url     : https://prove2.me/submissions/65c885aa-e5f6-4d9b-bb86-25d8c288cf49

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b n : ℝ)
  (h₀ : 64 - 8 * a + b = 0)
  (h₁ : a = n + 8)
  (h₂ : b = 8 * n) :
  64 - 8 * a + b = 0 := by
  (intros; simp_all)
