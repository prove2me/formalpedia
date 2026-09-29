-- Prove2me | solution 1 for lean_workbook_plus_31942
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:37.718059+00:00
-- url     : https://prove2.me/submissions/36b37ca2-6ce8-4936-8cc8-8c71656e72aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h : ∀ x z : ℝ, f x + f (2 * z) = f (x + 2 * z)) : ∀ x z : ℝ, f x + f (2 * z) = f (x + 2 * z) := by
  (intros; simp_all)
