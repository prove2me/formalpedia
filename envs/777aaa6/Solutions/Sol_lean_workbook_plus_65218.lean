-- Prove2me | solution 1 for lean_workbook_plus_65218
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:59.171704+00:00
-- url     : https://prove2.me/submissions/aeb1d876-5170-4b9e-9956-e8d62dba52dc

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℤ) : n = n := by
  norm_num
