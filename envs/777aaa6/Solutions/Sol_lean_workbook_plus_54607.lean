-- Prove2me | solution 1 for lean_workbook_plus_54607
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:42.657939+00:00
-- url     : https://prove2.me/submissions/5d97bfa6-215a-4a52-bffa-d74f07da4e8a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 20^2 + 21^2 = 29^2 := by
  norm_num
