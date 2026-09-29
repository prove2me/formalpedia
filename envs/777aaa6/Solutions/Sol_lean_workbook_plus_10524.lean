-- Prove2me | solution 1 for lean_workbook_plus_10524
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:45.361069+00:00
-- url     : https://prove2.me/submissions/3a038abb-c691-4f40-9678-b6ddb11b21ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h : ∀ x, f x / x ^ 2 = 0) : ∀ x, f x / x = 0 := by
  (intros; simp_all)
