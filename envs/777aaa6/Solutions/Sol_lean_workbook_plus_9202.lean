-- Prove2me | solution 1 for lean_workbook_plus_9202
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:57.120383+00:00
-- url     : https://prove2.me/submissions/cfc19a4e-8d4f-4b64-9308-d6b9af022bcd

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (hab : a ≥ -1) (hbc : b ≥ -1) (hcd : c ≥ -1) (hda : d ≥ -1) : a^3 + b^3 + c^3 + d^3 ≥ (3/4 : ℝ) * (a + b + c + d) - 1 := by
  have ha : (a - 1/2)^2 * (a + 1) ≥ 0 := mul_nonneg (sq_nonneg _) (by linarith)
  have hb : (b - 1/2)^2 * (b + 1) ≥ 0 := mul_nonneg (sq_nonneg _) (by linarith)
  have hc : (c - 1/2)^2 * (c + 1) ≥ 0 := mul_nonneg (sq_nonneg _) (by linarith)
  have hd : (d - 1/2)^2 * (d + 1) ≥ 0 := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [ha, hb, hc, hd]
