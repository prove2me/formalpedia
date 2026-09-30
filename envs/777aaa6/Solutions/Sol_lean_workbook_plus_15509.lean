-- Prove2me | solution 1 for lean_workbook_plus_15509
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:44:38.802904+00:00
-- url     : https://prove2.me/submissions/d8614487-d197-42d9-922c-dbdad0365a4a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c >= 3) : a^2 + b^2 + c^2 >= 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c - 3)]
