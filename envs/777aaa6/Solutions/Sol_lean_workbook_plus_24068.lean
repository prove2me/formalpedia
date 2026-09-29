-- Prove2me | solution 1 for lean_workbook_plus_24068
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:48.96342+00:00
-- url     : https://prove2.me/submissions/5cd07b95-e059-4125-bd55-295f8bc374c1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (c : ℝ) (h₁ : ∀ x, f x = c) (h₂ : ∀ x y, x * f x - y * f y = (x - y) * f (x + y)) : ∀ x, f x = c := by
  (intros; simp_all)
