-- Prove2me | solution 1 for lean_workbook_plus_55632
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:03:18.239367+00:00
-- url     : https://prove2.me/submissions/e90f4161-9583-4f86-927f-7523b5cdca8f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c P : ℝ) (h₁ : P = 2 * (a * b + b * c + c * a)) : (a + b + c) ^ 3 / P = (a + b + c) ^ 3 / (2 * (a * b + b * c + c * a)) := by
  (intros; simp_all)
