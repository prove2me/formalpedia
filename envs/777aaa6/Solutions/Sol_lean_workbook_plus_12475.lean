-- Prove2me | solution 1 for lean_workbook_plus_12475
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:58.242729+00:00
-- url     : https://prove2.me/submissions/bd622ba2-67cf-4d60-b330-74a910b78cb5

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^30) % 1000 = 824 := by
  norm_num
