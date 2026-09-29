-- Prove2me | solution 1 for lean_workbook_plus_59700
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:50.008332+00:00
-- url     : https://prove2.me/submissions/c7f63bef-4abb-4b59-9f58-211692e0f093

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (f : ℝ → ℝ) (h₁ : ∀ x, f x = x + a) : ∀ x, f x = x + a := by
  (intros; simp_all)
