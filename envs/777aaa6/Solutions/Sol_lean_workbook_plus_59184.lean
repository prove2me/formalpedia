-- Prove2me | solution 1 for lean_workbook_plus_59184
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:48:26.38451+00:00
-- url     : https://prove2.me/submissions/9774f4e7-3ffc-46e6-ab72-e319d56ef3d3

import Mathlib.Analysis.Complex.Basic

theorem solution    (a b : ℝ)
    (h₁ : a * b < 0)
    : (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0) := by
  exact mul_neg_iff.mp h₁
