-- Prove2me | solution 1 for lean_workbook_plus_82601
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:05.011298+00:00
-- url     : https://prove2.me/submissions/dc4dab43-5823-490b-b47a-d13691b57394

import Mathlib

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : 3 ≥ 1/x + 1/y + 1/z) :
    3 * (1/x + 1/y + 1/z) ≥ (1/x + 1/y + 1/z)^2 := by
  have hs : 0 ≤ 1/x + 1/y + 1/z := by positivity
  have hp := mul_nonneg hs (sub_nonneg.mpr h)
  nlinarith
