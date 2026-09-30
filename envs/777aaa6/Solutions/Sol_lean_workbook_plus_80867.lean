-- Prove2me | solution 1 for lean_workbook_plus_80867
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:09.493062+00:00
-- url     : https://prove2.me/submissions/47644ea3-6982-4ba5-be32-49395d38f2dc

import Mathlib

theorem solution (a b c x y : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = a * x^2 + b * x + c) (h₁ : x ≠ y) :
    f x - f y = (x - y) * (a * (x + y) + b) := by
  rw [h₀ x, h₀ y]
  ring
