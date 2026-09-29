-- Prove2me | solution 1 for lean_workbook_plus_28688
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:25.622786+00:00
-- url     : https://prove2.me/submissions/e71b96a4-f000-49e5-8aa8-f18e1f33c02e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f > 0) (h : ∀ x > 0, f x = x) : ∀ x > 0, f x = x := by
  (intros; simp_all)
