-- Prove2me | solution 1 for lean_workbook_plus_57772
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:40:59.228573+00:00
-- url     : https://prove2.me/submissions/cc61aa89-c035-4290-832c-9aa69e12b833

import Mathlib.Analysis.Complex.Basic

theorem solution : 3^(2001) * (3 - 1) = 2 * 3^(2001) := by
  norm_num [mul_comm]
