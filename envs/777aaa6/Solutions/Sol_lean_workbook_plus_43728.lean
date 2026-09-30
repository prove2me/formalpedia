-- Prove2me | solution 1 for lean_workbook_plus_43728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:35.159788+00:00
-- url     : https://prove2.me/submissions/8dfcf9d0-7027-4475-8a86-4d9612a6c905

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a ≥ 3 / 2) (hb : b ≥ 3 / 2) (hc : c ≥ 3 / 2) : a + 2 * b + 3 * c ≥ 9 / 8 * (1 / a + 2 / b + 3 / c + 4) := by
  have h1 : 1 / a ≤ (8 * a - 6) / 9 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h2 : 2 / b ≤ 2 * (8 * b - 6) / 9 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h3 : 3 / c ≤ 3 * (8 * c - 6) / 9 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  linarith
