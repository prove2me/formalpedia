-- Prove2me | solution 1 for lean_workbook_plus_81514
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:08.150745+00:00
-- url     : https://prove2.me/submissions/9b6bdaa5-680c-4567-9d14-bb50e9ec15c0

import Mathlib

theorem solution (a b c d e : ℝ)
    (h1 : a * b + b * c + c * d + d * e + e * a = 1)
    (h2 : a * c + b * d + c * e + d * a + e * b = -3) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 ≥ 4 := by
  nlinarith [sq_nonneg (a + b + c + d + e)]
