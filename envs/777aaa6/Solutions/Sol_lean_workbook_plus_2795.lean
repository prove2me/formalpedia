-- Prove2me | solution 1 for lean_workbook_plus_2795
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:53.363181+00:00
-- url     : https://prove2.me/submissions/970a9c4b-ee68-4719-9759-12be46193e15

import Mathlib

theorem solution (a b c x y z : ℝ) :
    (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a * z - c * x), sq_nonneg (b * z - c * y)]
