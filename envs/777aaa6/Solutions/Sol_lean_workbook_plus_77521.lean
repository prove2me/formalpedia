-- Prove2me | solution 1 for lean_workbook_plus_77521
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:35.067317+00:00
-- url     : https://prove2.me/submissions/09d099c8-a0bb-4fe0-9626-2a4dd1e7251e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℝ) (hx : 0 < x) : x = x := by
  norm_num
