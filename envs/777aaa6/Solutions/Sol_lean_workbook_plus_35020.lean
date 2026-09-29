-- Prove2me | solution 1 for lean_workbook_plus_35020
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:14.85611+00:00
-- url     : https://prove2.me/submissions/00f2e2f1-59b6-4d77-8bce-d1f9a6f01b79

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c * x ^ 2) : ∀ x, f x = c * x ^ 2 := by
  (intros; simp_all)
