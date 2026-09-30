-- Prove2me | solution 1 for lean_workbook_plus_2804
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:51.576789+00:00
-- url     : https://prove2.me/submissions/4b83a3f7-1ebc-47e2-bcae-dffd9d3c5203

import Mathlib

theorem solution (x y z : ℝ) (h₀ : 2 ≤ x ∧ x ≤ 3) (h₁ : y = 4 - x)
    (h₂ : z = -1) : x ^ 2 + y ^ 2 + z ^ 2 ≤ 11 := by
  subst y
  subst z
  nlinarith [mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
