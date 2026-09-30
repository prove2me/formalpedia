-- Prove2me | solution 1 for lean_workbook_plus_49560
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:15:48.146868+00:00
-- url     : https://prove2.me/submissions/7a0b2a8e-02c0-414e-adfd-a03d4b42f990

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a + b + c = 3) : (a * b + b * c + c * a - 3) ^ 2 ≥ 9 * (a * b * c - 1) := by
  have hc : c = 3 - a - b := by linarith
  subst hc
  nlinarith [sq_nonneg ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2 / 4 + 5 * (b - 1) / 4),
    sq_nonneg ((a - 1) * (b - 1) + (b - 1)^2 / 2 + 13 * (a - 1) / 6 + 4 * (b - 1) / 3),
    sq_nonneg ((b - 1)^2 - 2 * (a - 1) / 3 - 7 * (b - 1) / 3),
    sq_nonneg ((a - 1) - 17 * (b - 1) / 41),
    sq_nonneg (b - 1)]
