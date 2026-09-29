-- Prove2me | solution 1 for lean_workbook_plus_60257
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:13.536586+00:00
-- url     : https://prove2.me/submissions/46d044ca-23f2-4d4d-9791-99e37149ff81

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : a = 0 ∧ b = 0 ∧ c = 0)
  (h₁ : f a + b + c = 0)
  : f 0 = 0 := by
  (intros; simp_all)
