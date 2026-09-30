-- Prove2me | solution 1 for lean_workbook_plus_62980
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:32:49.190892+00:00
-- url     : https://prove2.me/submissions/96b3220b-089c-4908-b7ec-b3558765cf59

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : (a + 1) * (b + 1) * (c + 1) = 8) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a * b * c ≤ 1 := by
  have h1 : 4 * a ≤ (a + 1) ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  have h2 : 4 * b ≤ (b + 1) ^ 2 := by nlinarith [sq_nonneg (b - 1)]
  have h3 : 4 * c ≤ (c + 1) ^ 2 := by nlinarith [sq_nonneg (c - 1)]
  have h12 : (4 * a) * (4 * b) ≤ (a + 1) ^ 2 * (b + 1) ^ 2 :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have h123 : (4 * a) * (4 * b) * (4 * c) ≤ (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 :=
    mul_le_mul h12 h3 (by positivity) (by positivity)
  have hsq : (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 = 64 := by
    calc (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 = ((a + 1) * (b + 1) * (c + 1)) ^ 2 := by ring
      _ = 8 ^ 2 := by rw [h]
      _ = 64 := by norm_num
  nlinarith [h123, hsq]
