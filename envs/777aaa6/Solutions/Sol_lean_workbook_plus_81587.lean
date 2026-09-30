-- Prove2me | solution 1 for lean_workbook_plus_81587
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:28.287302+00:00
-- url     : https://prove2.me/submissions/80140e23-a0fb-4cf7-be1a-29eafe8541dd

import Mathlib

theorem solution (n : ℕ) (h₀ : 0 < n)
    (h₁ : (2 : ℝ) / (2 + 3 * n) = 1 / 7) : n = 4 := by
  have hd : (2 : ℝ) + 3 * n ≠ 0 := by positivity
  have hm := (div_eq_iff hd).mp h₁
  have hn : (n : ℝ) = 4 := by linarith
  exact_mod_cast hn
