-- Prove2me | solution 1 for lean_workbook_plus_44214
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:57.14939+00:00
-- url     : https://prove2.me/submissions/cf4ce6bd-2b52-4871-81e5-6819b4f55c7d

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) : b * c + a * c + a * b + a * b * c ≥ 4 := by
  have h1 : 1 / a + 1 / b + 1 / c = b * c + a * c + a * b := by
    field_simp
    nlinarith [habc]
  rw [h1] at h
  have hs : a + b + c > 0 := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), hs, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
