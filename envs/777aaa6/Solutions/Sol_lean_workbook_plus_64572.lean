-- Prove2me | solution 1 for lean_workbook_plus_64572
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:24.63828+00:00
-- url     : https://prove2.me/submissions/fd0c75f2-8a7c-476a-aad6-ebfdc6bf0d80

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h : Set.range f = {0}) : ∀ x, f x = 0 := by
  (intros; simp_all)
