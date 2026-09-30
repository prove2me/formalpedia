-- Prove2me | solution 1 for lean_workbook_plus_1961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:51.422523+00:00
-- url     : https://prove2.me/submissions/d5265af5-6690-49a7-9369-c7466c9e6eb5

import Mathlib

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / (a + b) + b ^ 2 / (b + c) ≥ (3 * a + 2 * b - c) / 4 := by
  have h₁ : (3 * a - b) / 4 ≤ a ^ 2 / (a + b) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b)]
  have h₂ : (3 * b - c) / 4 ≤ b ^ 2 / (b + c) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg (b - c)]
  linarith
