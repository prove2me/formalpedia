-- Prove2me | solution 1 for lean_workbook_plus_9284
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:23:41.359812+00:00
-- url     : https://prove2.me/submissions/a874f7da-7cdb-4618-ace8-6ea42325c8ec

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a * Real.sqrt a + b * Real.sqrt b + c * Real.sqrt c >= 3 → a * b * c + 2 >= 9 / (a ^ 3 + b ^ 3 + c ^ 3) := by
  intro _
  have hsum : a ^ 3 + b ^ 3 + c ^ 3 ≥ 3 := by
    nlinarith [mul_nonneg (add_pos (add_pos ha hb) hc).le (sq_nonneg (a - b)),
      mul_nonneg (add_pos (add_pos ha hb) hc).le (sq_nonneg (b - c)),
      mul_nonneg (add_pos (add_pos ha hb) hc).le (sq_nonneg (c - a))]
  have hpos : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by positivity
  rw [habc, ge_iff_le, div_le_iff₀ hpos]
  nlinarith
