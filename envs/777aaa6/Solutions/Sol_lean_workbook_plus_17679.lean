-- Prove2me | solution 1 for lean_workbook_plus_17679
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:32.090545+00:00
-- url     : https://prove2.me/submissions/56674f46-54be-405f-ae5e-21dcf73f9901

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℝ) (hp : 1 ≤ p) : 2 * p ^ 3 + 4 * p + 1 ≥ 6 * p ^ 2 := by
  nlinarith [sq_nonneg (p - 1), sq_nonneg (p - 2), mul_nonneg (sub_nonneg.2 hp) (sq_nonneg (p - 3 / 2)),
    mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hp)]
