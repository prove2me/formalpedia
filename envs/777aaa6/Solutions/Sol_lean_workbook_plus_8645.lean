-- Prove2me | solution 1 for lean_workbook_plus_8645
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:22.138573+00:00
-- url     : https://prove2.me/submissions/1474354f-81bb-459d-a805-5d69e3e8fe8f

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℤ) (h₁ : x^2 - 1 = 3 * y^2) : ∃ x y : ℤ, x^2 - 1 = 3 * y^2 ∧ y ≠ 0 :=
  ⟨2, 1, by norm_num, by norm_num⟩
