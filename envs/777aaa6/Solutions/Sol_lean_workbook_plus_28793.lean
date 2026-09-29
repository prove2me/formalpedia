-- Prove2me | solution 1 for lean_workbook_plus_28793
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:08.665035+00:00
-- url     : https://prove2.me/submissions/e3e43e14-1aef-4be0-876b-00f6bc1196e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ) (h : ∀ x, f x = a * x) : ∀ x, f x = a * x := by
  (intros; simp_all)
