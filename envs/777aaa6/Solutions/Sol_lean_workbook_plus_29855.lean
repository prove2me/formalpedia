-- Prove2me | solution 1 for lean_workbook_plus_29855
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:55.56178+00:00
-- url     : https://prove2.me/submissions/b0df74b2-eff4-4d7b-9482-870dc391a2d2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (h : ∀ x, f (x + 1) = f x + 1) : f (x + 1) = f x + 1 := by
  (intros; simp_all)
