-- Prove2me | solution 2 for lean_workbook_plus_54522
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:41:04.931334+00:00
-- url     : https://prove2.me/submissions/cec71b06-e435-46ee-b906-7b41c87892ad

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (a + b + c) ^ 2 / (a * b + b * c + a * c) := by
  have key : a / b + b / c + c / a = (a ^ 2 * c + a * b ^ 2 + b * c ^ 2) / (a * b * c) := by
    field_simp
  rw [key, ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg ha.le (sq_nonneg c)) (sq_nonneg (a - b)),
    mul_nonneg (mul_nonneg hb.le (sq_nonneg a)) (sq_nonneg (b - c)),
    mul_nonneg (mul_nonneg hc.le (sq_nonneg b)) (sq_nonneg (c - a))]
