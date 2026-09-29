-- Prove2me | solution 1 for lean_workbook_plus_45600
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:37:30.188286+00:00
-- url     : https://prove2.me/submissions/0c2a0af6-e15e-452b-a4c7-799e8a08635c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℤ → ℤ) (h₁ : ∀ x, q x = p (x - 1)) (h₂ : ∀ x, p (x^2 - 1) = (p (x - 1))^2) : ∀ x, q (x^2) = (q x)^2 := by
  (intros; simp_all)
