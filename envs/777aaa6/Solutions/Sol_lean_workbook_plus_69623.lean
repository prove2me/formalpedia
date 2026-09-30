-- Prove2me | solution 1 for lean_workbook_plus_69623
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:20.009439+00:00
-- url     : https://prove2.me/submissions/2dad36a4-af37-4201-b3a3-c26034fa12f5

import Mathlib

theorem solution (a b c : ℝ) (h : a + b + c = 3) :
    (3 - a) ^ 2 + (3 - b) ^ 2 + (3 - c) ^ 2 ≥ 12 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
