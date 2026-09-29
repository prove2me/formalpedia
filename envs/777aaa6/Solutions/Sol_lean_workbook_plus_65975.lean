-- Prove2me | solution 1 for lean_workbook_plus_65975
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:18.301873+00:00
-- url     : https://prove2.me/submissions/40e768e4-ae7b-4a79-bed7-a42ae75f4403

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x a b : ℝ) (h₁ : a = (x + 1) / (x - 2)) (h₂ : b = (x - 2) / (x + 1)) (h₃ : f a + 3 * f b = x) (h₄ : f b + 3 * f a = -x + 1) : f b = (4 * x - 1) / 8 := by
  (intros; linarith)
