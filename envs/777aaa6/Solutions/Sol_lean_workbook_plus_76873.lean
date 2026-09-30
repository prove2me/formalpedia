-- Prove2me | solution 1 for lean_workbook_plus_76873
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:01.557347+00:00
-- url     : https://prove2.me/submissions/6d770a30-2f2b-482f-b250-934f57cd9c93

import Mathlib

theorem solution (a b c d e f : ℝ) :
    (a + d) ^ 2 + (b + e) ^ 2 + (c + f) ^ 2 ≥
      (a + d) * (b + e) + (a + d) * (c + f) + (b + e) * (c + f) := by
  nlinarith [sq_nonneg (a + d - (b + e)), sq_nonneg (a + d - (c + f)),
    sq_nonneg (b + e - (c + f))]
