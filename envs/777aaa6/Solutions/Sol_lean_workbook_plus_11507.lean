-- Prove2me | solution 1 for lean_workbook_plus_11507
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:24.709721+00:00
-- url     : https://prove2.me/submissions/75ee1e32-1cae-4706-a67a-ae1fd5fea2ea

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k₁ k₂ k₃ k₄ a b c : ℝ) : k₁ * a * b * c + k₂ * (a * b + a * c + b * c) + k₃ * (a + b + c) + k₄ = 0 → a = a ∧ b = b ∧ c = c := by
  norm_num
