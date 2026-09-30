-- Prove2me | solution 1 for lean_workbook_plus_3463
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:48:09.197167+00:00
-- url     : https://prove2.me/submissions/48f3fa58-545f-4e28-a1cd-47c62c7c169f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (3^33 + 77) % 100 = 0 := by
  norm_num
