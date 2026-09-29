-- Prove2me | solution 1 for lean_workbook_plus_3284
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:14:50.654086+00:00
-- url     : https://prove2.me/submissions/225f73c1-d00e-4198-b609-f3635bd1a225

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c) : ∀ x, f x = c := by
  (intros; simp_all)
