-- Prove2me | solution 1 for lean_workbook_plus_65999
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:01.826292+00:00
-- url     : https://prove2.me/submissions/2a09e5d2-0d2f-48cd-8397-aa82bc21c218

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) : (∀ v : ℝ × ℝ, ∃ a b : ℝ, v = (a, b)) ∨ (∀ v : ℝ × ℝ, ∃ a b : ℝ, v = (a, b) ∨ v = (b, -a)) := by
  norm_num
