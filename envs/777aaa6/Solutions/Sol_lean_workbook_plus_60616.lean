-- Prove2me | solution 1 for lean_workbook_plus_60616
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:46:14.810673+00:00
-- url     : https://prove2.me/submissions/b2cea36b-2c6d-438c-a604-79092c8f82a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (g : ℝ → ℝ) (h₁ : x > 0) (h₂ : g x = g (1/x)) : g x = g (1/x) := by
  (intros; simp_all)
