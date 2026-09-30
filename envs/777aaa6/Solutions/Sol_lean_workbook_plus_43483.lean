-- Prove2me | solution 1 for lean_workbook_plus_43483
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:03.26175+00:00
-- url     : https://prove2.me/submissions/d84eef87-8102-4e05-bea0-20fc131ce866

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3 * 7^5 < 5^7 := by
  norm_num
