-- Prove2me | solution 1 for lean_workbook_plus_65434
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:53.735401+00:00
-- url     : https://prove2.me/submissions/bdaddc43-a4f8-4b98-b66f-3189b8c52ce1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h₁ : a + b + c + d = 5 / 2) (h₂ : a^2 + b^2 + c^2 + d^2 = 25 / 12) (h₃ : a * b * c * d = 125 / 216) : a * b * c * d = 125 / 216 ∧ a + b + c + d = 5 / 2 ∧ a^2 + b^2 + c^2 + d^2 = 25 / 12 := by
  (intros; simp_all)
