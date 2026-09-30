-- Prove2me | solution 1 for lean_workbook_plus_73537
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:34.402945+00:00
-- url     : https://prove2.me/submissions/f7af9731-ad59-4c6c-aea8-a32b820e5c13

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 13 ^ 157 - 14 ^ 156 < 2001 := by
  norm_num
