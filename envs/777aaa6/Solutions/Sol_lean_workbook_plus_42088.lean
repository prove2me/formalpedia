-- Prove2me | solution 1 for lean_workbook_plus_42088
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:52.148933+00:00
-- url     : https://prove2.me/submissions/c2b41de7-f247-4d57-8ade-bb6a957d7b0e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^3 + b^3 + c^3 - 3*a*b*c ≥ 2 * ((b + c) / 2 - a)^3 := by
  nlinarith [mul_nonneg ha (sq_nonneg ((b + c) / 2 - a)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (b - c))]
