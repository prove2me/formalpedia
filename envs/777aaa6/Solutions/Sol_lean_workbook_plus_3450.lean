-- Prove2me | solution 1 for lean_workbook_plus_3450
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:12.304141+00:00
-- url     : https://prove2.me/submissions/823165f4-b05c-478d-8775-826bfc1500a4

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) : |a * c - b * d| ≤ 1 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (a + c), sq_nonneg (b - d)]
  · nlinarith [sq_nonneg (a - c), sq_nonneg (b + d)]
