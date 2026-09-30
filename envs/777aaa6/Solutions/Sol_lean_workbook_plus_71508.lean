-- Prove2me | solution 1 for lean_workbook_plus_71508
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:53.585809+00:00
-- url     : https://prove2.me/submissions/43f9730d-cbb0-42ad-b55a-ce04b6f4a7f2

import Mathlib

theorem solution (x : ℝ) (f : ℝ → ℝ) (h₀ : x ≠ 0)
    (h₁ : 2 * f x * f (-x) = 2 - x * f (-x) + x)
    (h₂ : 2 * f x * f (-x) = 2 + x * f x - x) :
    f (-x) = 2 - f x := by
  have hp : x * (f (-x) - (2 - f x)) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left h₀)

#print axioms solution
