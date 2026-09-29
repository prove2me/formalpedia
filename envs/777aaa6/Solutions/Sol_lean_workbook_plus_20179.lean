-- Prove2me | solution 1 for lean_workbook_plus_20179
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:14.186941+00:00
-- url     : https://prove2.me/submissions/6c85e395-66fb-4e65-b3db-7018d2f84ccc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (m n : ℝ) (k : ℝ) (h₁ : b - a = k) (h₂ : n - m = k) (h₃ : a + b ≥ m + n) : a ≥ m := by
  (intros; linarith)
