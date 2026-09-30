-- Prove2me | solution 1 for lean_workbook_plus_81504
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:08.979657+00:00
-- url     : https://prove2.me/submissions/65dae12e-843a-415e-8d6a-74cf8761370c

import Mathlib

theorem solution {a b c x y : ℝ} (hx : x = a^2 + b^2 + c^2)
    (hy : y = a * b + b * c + c * a) : x ≥ y := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
