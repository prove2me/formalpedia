-- Prove2me | solution 1 for lean_workbook_plus_52777
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:51.752589+00:00
-- url     : https://prove2.me/submissions/9f6e20be-f681-4f4b-a22b-4809b6e35228

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: ∀ x y : ℝ, x > 0 ∧ y > 0 → f x + f y = 2 * f (x + y) / 2) : ∀ x y : ℝ, x > 0 ∧ y > 0 → f x + f y = 2 * f (x + y) / 2 := by
  (intros; simp_all)
