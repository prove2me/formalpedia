-- Prove2me | solution 1 for lean_workbook_plus_55000
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:15.88922+00:00
-- url     : https://prove2.me/submissions/7a1ad515-e303-4527-9d8d-922e54fa63b9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ) (h₁ : a = 1) (h₂ : f a = 0) : f 1 = 0 := by
  (intros; simp_all)
