-- Prove2me | solution 1 for lean_workbook_plus_38886
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:09.990622+00:00
-- url     : https://prove2.me/submissions/e4bfcc6a-1384-4c09-b839-27b7747f5e06

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y t : ℝ) (h₁ : t ≠ 9) (h₂ : x = t - 2) (h₃ : y = t - 1) : y = -(t - 5) / (t - 9) * (x - t + 2) + t - 1 := by
  (intros; simp_all)
