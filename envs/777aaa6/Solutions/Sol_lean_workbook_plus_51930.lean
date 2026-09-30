-- Prove2me | solution 1 for lean_workbook_plus_51930
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:13.348713+00:00
-- url     : https://prove2.me/submissions/a84d5803-208d-4d05-8c47-e94659f6f80a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c) (h2 : a * b * c ≤ 1 / 4) (h3 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 < 9) : ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a := by
  exact ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
