-- Prove2me | solution 1 for lean_workbook_plus_23545
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:04.532883+00:00
-- url     : https://prove2.me/submissions/f8a5c287-c86b-4fd5-9203-b568dd02c118

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 1000^1000 > 1001^999 := by
  omega
