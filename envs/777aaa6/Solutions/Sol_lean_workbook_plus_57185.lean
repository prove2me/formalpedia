-- Prove2me | solution 1 for lean_workbook_plus_57185
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:25:43.839739+00:00
-- url     : https://prove2.me/submissions/f2d9e68a-a131-48a8-9aa7-607997ba962e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c) (h₂ : a * b * c ≤ 1 / 4) (h₃ : 1 / a^2 + 1 / b^2 + 1 / c^2 < 9) : ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a :=
  ⟨1, 1, 1, by norm_num⟩
