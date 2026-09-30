-- Prove2me | solution 1 for lean_workbook_plus_45111
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:02.506942+00:00
-- url     : https://prove2.me/submissions/451fb2b4-a292-4b23-9655-4494122adfd1

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ 2 * ((b + c) / 2 - a)^3 := by
  nlinarith [mul_nonneg ha.le (sq_nonneg (a - (b + c) / 2)),
    mul_nonneg (add_pos hb hc).le (sq_nonneg (b - c)),
    mul_nonneg ha.le (sq_nonneg (b - c))]
