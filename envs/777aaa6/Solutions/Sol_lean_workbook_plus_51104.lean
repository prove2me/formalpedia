-- Prove2me | solution 1 for lean_workbook_plus_51104
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:51.042565+00:00
-- url     : https://prove2.me/submissions/0f26d1ff-e18a-4d97-814f-77eb4cd71ab0

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ → ℝ) (i : ℕ) :
  x i * x (i + 2) ≤ (x i ^ 2 + x (i + 2) ^ 2) / 2 := by
  nlinarith [sq_nonneg (x i - x (i + 2))]
