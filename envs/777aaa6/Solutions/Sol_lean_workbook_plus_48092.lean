-- Prove2me | solution 1 for lean_workbook_plus_48092
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:55.759731+00:00
-- url     : https://prove2.me/submissions/257f3be8-f6ea-4202-b234-416e357e39dc

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} : (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 + (a ^ 4 + b ^ 4 + c ^ 4 - a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0 := by
  nlinarith [sq_nonneg ((a - b) ^ 2), sq_nonneg ((b - c) ^ 2), sq_nonneg ((c - a) ^ 2),
    sq_nonneg (a ^ 2 - b * c), sq_nonneg (b ^ 2 - c * a), sq_nonneg (c ^ 2 - a * b),
    sq_nonneg (a ^ 2 + b * c), sq_nonneg (b ^ 2 + c * a), sq_nonneg (c ^ 2 + a * b),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a * b + b * c), sq_nonneg (b * c + c * a), sq_nonneg (c * a + a * b),
    sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
