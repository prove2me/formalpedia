-- Prove2me | solution 1 for lean_workbook_plus_48169
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:25.525637+00:00
-- url     : https://prove2.me/submissions/2bffd1b4-598e-42c0-ad1f-eaac0ccb2b90

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℚ) (hx : 0 < x) : x = x := by
  norm_num
