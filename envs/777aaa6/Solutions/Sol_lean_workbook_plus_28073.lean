-- Prove2me | solution 1 for lean_workbook_plus_28073
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:01.006008+00:00
-- url     : https://prove2.me/submissions/b67263a0-fa9b-4369-a712-8ca5ed0c1b7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) (h₁ : 4 + Real.sqrt 6 < k) (h₂ : k ≤ 7 + Real.sqrt 3) : 4 + Real.sqrt 6 < k ∧ k ≤ 7 + Real.sqrt 3 := by
  (intros; simp_all)
