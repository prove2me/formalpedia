-- Prove2me | solution 1 for lean_workbook_plus_2230
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:31.709209+00:00
-- url     : https://prove2.me/submissions/38e5f22a-9a9b-4f97-b5fd-593f19e780bb

import Mathlib

theorem solution (a b c : ℝ) :
    (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥
      8 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) := by
  nlinarith [sq_nonneg ((a - b) ^ 2), sq_nonneg ((b - c) ^ 2),
    sq_nonneg ((c - a) ^ 2)]
